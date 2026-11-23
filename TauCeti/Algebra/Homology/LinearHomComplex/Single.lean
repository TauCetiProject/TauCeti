/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import TauCeti.Algebra.Homology.Embedding.Regrade
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Algebra.Homology.UniversalCoefficient.Basic
public import TauCeti.Algebra.Ring.NegOnePow

/-!
# The Hom complex into an object placed in degree zero

Let `K` be a cochain complex indexed by `ℤ` in a `k`-linear abelian category `C`, and let `Y : C`.
The `k`-linear Hom complex `Hom(K, Y[0])` (`CochainComplex.linearHomComplex`) into the complex `Y`
concentrated in degree zero is the dual complex of `K` with coefficients in `Y`: in degree `i` its
term is the module of morphisms `K⁻ⁱ ⟶ Y` (`HomComplex.Cochain.toSingleEquiv`), and its
differential is `f ↦ (-1)^(i+1) f ∘ d`. For `C = ModuleCat R` and `Y = R` this is the dual of a
complex of `R`-modules, reversing cochain degrees.

Reading `K` as the chain complex `K⁻` with `K⁻ᵢ = K⁻ⁱ` (the restriction along `n ↦ -n`, as in
Mathlib's `ChainComplex.cochainComplexEquivalence`), the dual complex is isomorphic to the linear
Yoneda complex `Hom(K⁻, Y)` (`ChainComplex.linearYonedaObj`), whose differential has no sign. The
isomorphism `CochainComplex.linearHomComplexSingleIso` multiplies by `(-1)^(i(i+1)/2)` in degree
`i`. Through it, the Kronecker map and the universal coefficient sequence of chain complexes
(`TauCeti.Algebra.Homology.Kronecker` and `TauCeti.Algebra.Homology.UniversalCoefficient.Basic`)
give the universal coefficient sequence of the dual complex,

`0 ⟶ Ext¹(H¹⁻ⁱ(K), Y) ⟶ Hⁱ(Hom(K, Y[0])) ⟶ (H⁻ⁱ(K) ⟶ Y) ⟶ 0`,

exact when the cocycles of `K` in degrees `1 - i` and `-i` split off and those in degree `1 - i`
are projective, for instance for a complex of free abelian groups. For an injective object `Y`,
such as a field over itself, the Kronecker map is an isomorphism in every degree: the cohomology
of the dual complex is the dual of the cohomology. The sign is corrected in the Kronecker map
`CochainComplex.linearHomComplexSingleKronecker`, which evaluates a cocycle on cocycles of `K`
without any sign (`CochainComplex.homologyπ_linearHomComplexSingleKronecker`).

## Main definitions and results

* `CochainComplex.linearHomComplexSingleIso`: the isomorphism `Hom(K, Y[0]) ≅ Hom(K⁻, Y)`.
  The cycles and homology of `K⁻` are compared with those of `K` by
  `CochainComplex.restrictionDownIntUpIntCyclesIso` and
  `CochainComplex.restrictionDownIntUpIntHomologyIso`.
* `CochainComplex.linearHomComplexSingleKronecker`: the Kronecker map
  `Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)`, characterized by
  `CochainComplex.homologyπ_linearHomComplexSingleKronecker`.
* `CochainComplex.linearHomComplexSingleKronecker_bijective` and
  `CochainComplex.linearHomComplexSingleKroneckerEquiv`: the Kronecker map is bijective for an
  injective object `Y`.
* `CochainComplex.linearHomComplexSingleKronecker_surjective`: it is surjective when the cocycles
  of `K` split off in degree `-i`.
* `CochainComplex.linearHomComplexSingleExtToHomology` (characterized by
  `CochainComplex.linearHomComplexSingleExtToHomology_extClass_comp_mk₀`),
  `CochainComplex.linearHomComplexSingleExtToHomology_injective` and
  `CochainComplex.exact_linearHomComplexSingleExtToHomology_linearHomComplexSingleKronecker`: the
  `Ext¹` term of the universal coefficient sequence, and exactness at its first two places.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Theorem 3.2.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Theorem 3.6.5.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Abelian

namespace CochainComplex

open HomComplex

variable {C : Type*} [Category* C]

section Preadditive

variable [Preadditive C] [HasZeroObject C] (K : CochainComplex C ℤ) (Y : C)

/-- Precomposing the morphism `(K.restriction e).X i ⟶ Y` of a cochain to `Y[q]` with the
identification `K.X p ≅ (K.restriction e).X i` gives the morphism `K.X p ⟶ Y` of the same
cochain. -/
lemma HomComplex.Cochain.restrictionXIso_inv_comp_toSingleEquiv {ι : Type*}
    {c : ComplexShape ι} (e : c.Embedding (ComplexShape.up ℤ)) [e.IsRelIff] {i : ι} {p n q : ℤ}
    (hi : e.f i = p) (h : p + n = q) (h' : e.f i + n = q)
    (α : Cochain K ((singleFunctor C q).obj Y) n) :
    (K.restrictionXIso e hi).inv ≫ Cochain.toSingleEquiv h' α =
      Cochain.toSingleEquiv h α := by
  subst hi
  -- `restrictionXIso` is defined as an `eqToIso`, which is the identity once `hi` is `rfl`
  simp [restrictionXIso]

end Preadditive

variable [Abelian C]

section Ring

variable {k : Type*} [Ring k] [Linear k C] (K : CochainComplex C ℤ) (Y : C)

/-- The sign `(-1)^(i(i+1)/2)` relating the two differentials. -/
private def homSingleSign (i : ℤ) : ℤˣ := (i * (i + 1) / 2).negOnePow

/-- The index of `K⁻ᵢ = K⁻ⁱ` and the degree `i` add up to zero. -/
private lemma embeddingDownIntUpInt_f_add_self (i : ℤ) :
    ComplexShape.embeddingDownIntUpInt.f i + i = 0 := by
  simp

variable (k) in
/-- In degree `i`, a cochain of degree `i` from `K` to `Y` placed in degree `0` is a morphism
`K⁻ⁱ ⟶ Y`, here twisted by the sign `(-1)^(i(i+1)/2)`. -/
private def homSingleXEquiv (i : ℤ) :
    Cochain K ((singleFunctor C 0).obj Y) i ≃ₗ[k]
      ((K.restriction ComplexShape.embeddingDownIntUpInt).X i ⟶ Y) :=
  (Cochain.toSingleLinearEquiv (embeddingDownIntUpInt_f_add_self i)).trans
    (DistribMulAction.toLinearEquiv k _ (homSingleSign i))

/-- `CochainComplex.homSingleXEquiv` is `HomComplex.Cochain.toSingleEquiv` twisted by the sign. -/
private lemma homSingleXEquiv_apply (i : ℤ) (α : Cochain K ((singleFunctor C 0).obj Y) i) :
    homSingleXEquiv k K Y i α =
      homSingleSign i • Cochain.toSingleEquiv (embeddingDownIntUpInt_f_add_self i) α := by
  simp [homSingleXEquiv]

/-- The inverse of `CochainComplex.homSingleXEquiv` is `HomComplex.Cochain.toSingleMk` twisted by
the sign. -/
private lemma homSingleXEquiv_symm_apply (i : ℤ)
    (f : (K.restriction ComplexShape.embeddingDownIntUpInt).X i ⟶ Y) :
    (homSingleXEquiv k K Y i).symm f =
      homSingleSign i • Cochain.toSingleMk f (embeddingDownIntUpInt_f_add_self i) := by
  simp [homSingleXEquiv, Cochain.toSingleEquiv_symm_apply, Units.smul_def,
    Cochain.toSingleMk_smul]

variable (k) in
/-- `CochainComplex.homSingleXEquiv` as an isomorphism between the terms of degree `i` of the two
complexes. -/
private def homSingleXIso (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).X i ≅
      (ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).X i :=
  (homSingleXEquiv k K Y i).toModuleIso

/-- The isomorphisms `CochainComplex.homSingleXIso` commute with the differentials. -/
private lemma homSingle_comm (i : ℤ) (α : Cochain K ((singleFunctor C 0).obj Y) i) :
    (K.restriction ComplexShape.embeddingDownIntUpInt).d (i + 1) i ≫
        (homSingleSign i • Cochain.toSingleEquiv (embeddingDownIntUpInt_f_add_self i) α) =
      homSingleSign (i + 1) •
        Cochain.toSingleEquiv (embeddingDownIntUpInt_f_add_self (i + 1)) (δ i (i + 1) α) := by
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective α _ (embeddingDownIntUpInt_f_add_self i)
  rw [Cochain.δ_toSingleMk f (embeddingDownIntUpInt_f_add_self i) (i + 1)
    (ComplexShape.embeddingDownIntUpInt.f (i + 1)) (embeddingDownIntUpInt_f_add_self _)]
  simp [homSingleSign, Int.negOnePow_mul_succ_div_two_succ, smul_smul, mul_right_comm]

variable (k) in
/-- **The Hom complex into an object placed in degree zero is its linear Yoneda complex.** The
`k`-linear Hom complex from a cochain complex `K` indexed by `ℤ` to the single complex `Y[0]` is
isomorphic to `Hom(K⁻, Y)` (`ChainComplex.linearYonedaObj`), where `K⁻` is the chain complex with
`K⁻ᵢ = K⁻ⁱ` (the restriction of `K` along `n ↦ -n`). In degree `i` both terms are the morphisms
`K⁻ⁱ ⟶ Y`; the Hom complex has differential `f ↦ (-1)^(i+1) f ∘ d`, whereas the linear Yoneda
complex has differential `f ↦ f ∘ d`, so the isomorphism multiplies by `(-1)^(i(i+1)/2)` in
degree `i` (`CochainComplex.linearHomComplexSingleIso_hom_f_apply`). -/
def linearHomComplexSingleIso :
    linearHomComplex k K ((singleFunctor C 0).obj Y) ≅
      ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k Y :=
  Hom.isoOfComponents (homSingleXIso k K Y) (by
    rintro i _ rfl
    ext α
    exact homSingle_comm K Y i α)

/-- In degree `i`, `CochainComplex.linearHomComplexSingleIso` sends a cochain `α` of degree `i`
to the morphism `K⁻ⁱ ⟶ Y` it consists of (`HomComplex.Cochain.toSingleEquiv`), multiplied by the
sign `(-1)^(i(i+1)/2)`. -/
lemma linearHomComplexSingleIso_hom_f_apply (i : ℤ)
    (α : Cochain K ((singleFunctor C 0).obj Y) i) :
    (linearHomComplexSingleIso k K Y).hom.f i α =
      (i * (i + 1) / 2).negOnePow • Cochain.toSingleEquiv (neg_add_cancel i) α :=
  -- the component in degree `i` is `homSingleXEquiv`, read in `ModuleCat` through
  -- `LinearEquiv.toModuleIso`, whose underlying map is that linear equivalence by definition
  homSingleXEquiv_apply K Y i α

/-- `CochainComplex.linearHomComplexSingleIso_hom_f_apply`, with the morphism `K⁻ⁱ ⟶ Y` typed by
the index of the restriction `K⁻`, as the terms of `Hom(K⁻, Y)` are. -/
private lemma linearHomComplexSingleIso_hom_f_apply_restriction (i : ℤ)
    (α : Cochain K ((singleFunctor C 0).obj Y) i) :
    (linearHomComplexSingleIso k K Y).hom.f i α =
      homSingleSign i • Cochain.toSingleEquiv (embeddingDownIntUpInt_f_add_self i) α :=
  homSingleXEquiv_apply K Y i α

/-- In degree `i`, the inverse of `CochainComplex.linearHomComplexSingleIso` sends a morphism
`f : K⁻ⁱ ⟶ Y` to the cochain of degree `i` it defines (`HomComplex.Cochain.toSingleMk`),
multiplied by the sign `(-1)^(i(i+1)/2)`. -/
lemma linearHomComplexSingleIso_inv_f_apply (i : ℤ)
    (f : (K.restriction ComplexShape.embeddingDownIntUpInt).X i ⟶ Y) :
    (linearHomComplexSingleIso k K Y).inv.f i f =
      (i * (i + 1) / 2).negOnePow • Cochain.toSingleMk (p := -i) f (neg_add_cancel i) :=
  -- as for `CochainComplex.linearHomComplexSingleIso_hom_f_apply`, the inverse of the component in
  -- degree `i` is the inverse of `homSingleXEquiv` by definition
  homSingleXEquiv_symm_apply K Y i f

/-! ### The Kronecker map -/

variable (k) in
/-- The `k`-linear equivalence between the cohomology of the Hom complex `Hom(K, Y[0])` and that of
the linear Yoneda complex `Hom(K⁻, Y)` in degree `i`, induced by
`CochainComplex.linearHomComplexSingleIso` and corrected by the sign `(-1)^(i(i+1)/2)`, so that
it is induced by the identification `HomComplex.Cochain.toSingleEquiv` of the terms. -/
private def homSingleHomologyEquiv (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k]
      (ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k
        Y).homology i :=
  ((homologyFunctor _ _ i).mapIso (linearHomComplexSingleIso k K Y)).toLinearEquiv.trans
    (DistribMulAction.toLinearEquiv k _ (homSingleSign i))

/-- `CochainComplex.homSingleHomologyEquiv` sends the class of a cocycle `φ` of `Hom(K, Y[0])` to
the class of the cocycle of `Hom(K⁻, Y)` with the same underlying morphism `K⁻ⁱ ⟶ Y`. -/
private lemma homSingleHomologyEquiv_homologyπ (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i) :
    homSingleHomologyEquiv k K Y i
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ) =
      (ChainComplex.linearYonedaObj _ k Y).homologyπ i
        (homSingleSign i • cyclesMap (linearHomComplexSingleIso k K Y).hom i φ) := by
  simp [homSingleHomologyEquiv, moduleCat_homologyMap_homologyπ]

/-- The cocycle of `Hom(K⁻, Y)` of `CochainComplex.homSingleHomologyEquiv_homologyπ` has the
same underlying morphism `K⁻ⁱ ⟶ Y` as `φ`. -/
private lemma iCycles_homSingleSign_smul_cyclesMap (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i) :
    (ChainComplex.linearYonedaObj _ k Y).iCycles i
        (homSingleSign i • cyclesMap (linearHomComplexSingleIso k K Y).hom i φ) =
      Cochain.toSingleEquiv (embeddingDownIntUpInt_f_add_self i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) := by
  rw [Units.smul_def, map_zsmul, moduleCat_iCycles_cyclesMap_apply, ← Units.smul_def]
  exact Int.negOnePow_smul_negOnePow_smul _ _

variable (k) in
/-- **The Kronecker map** `Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)` of a cochain complex `K`
indexed by `ℤ`, evaluating the cohomology classes of the Hom complex into `Y` placed in degree
zero on the cohomology classes of `K`: a cocycle of degree `i` is a morphism `K⁻ⁱ ⟶ Y` vanishing
on coboundaries, and its restriction to the cocycles of `K` descends to `H⁻ⁱ(K)`
(`CochainComplex.homologyπ_linearHomComplexSingleKronecker`). It is the Kronecker map
`TauCeti.ChainComplex.kronecker` of the chain complex `K⁻` with `K⁻ᵢ = K⁻ⁱ`, transported along
`CochainComplex.linearHomComplexSingleIso`. -/
def linearHomComplexSingleKronecker (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i →ₗ[k] (K.homology (-i) ⟶ Y) :=
  (Linear.homCongr k (K.restrictionDownIntUpIntHomologyIso i (-i) (add_neg_cancel i))
    (Iso.refl Y)).toLinearMap ∘ₗ
    TauCeti.ChainComplex.kronecker k _ Y i ∘ₗ (homSingleHomologyEquiv k K Y i).toLinearMap

/-- **The Kronecker map on classes**: evaluating the class of a cocycle `φ` of `Hom(K, Y[0])` of
degree `i` on the class of a cocycle of `K` of degree `-i` is evaluating the morphism
`K⁻ⁱ ⟶ Y` underlying `φ` on that cocycle. -/
@[reassoc (attr := simp)]
lemma homologyπ_linearHomComplexSingleKronecker (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i) :
    K.homologyπ (-i) ≫ linearHomComplexSingleKronecker k K Y i
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ) =
      K.iCycles (-i) ≫ Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) := by
  simp only [linearHomComplexSingleKronecker, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, homSingleHomologyEquiv_homologyπ, homSingleSign, map_zsmul_unit,
    Linear.homCongr_apply, Iso.refl_hom, Category.comp_id, Linear.comp_units_smul,
    homologyπ_restrictionDownIntUpIntHomologyIso_inv_assoc,
    TauCeti.ChainComplex.kronecker_homologyπ, restriction_X, ComplexShape.embeddingDownIntUpInt_f,
    moduleCat_iCycles_cyclesMap_apply, linearHomComplexSingleIso_hom_f_apply_restriction,
    restrictionDownIntUpIntCyclesIso_inv_iCycles_assoc,
    Int.negOnePow_smul_negOnePow_smul]
  rw [HomComplex.Cochain.restrictionXIso_inv_comp_toSingleEquiv]

/-- **The universal coefficient theorem for injective coefficients**: for an injective object
`Y`, the Kronecker map `Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)` is bijective. -/
theorem linearHomComplexSingleKronecker_bijective [Injective Y] (i : ℤ) :
    Function.Bijective (linearHomComplexSingleKronecker k K Y i) := by
  rw [linearHomComplexSingleKronecker, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (LinearEquiv.bijective _).comp ((TauCeti.ChainComplex.kronecker_bijective i).comp
    (LinearEquiv.bijective _))

variable (k) in
/-- The Kronecker map as a `k`-linear equivalence `Hⁱ(Hom(K, Y[0])) ≃ₗ[k] (H⁻ⁱ(K) ⟶ Y)`, for an
injective object `Y`. -/
def linearHomComplexSingleKroneckerEquiv [Injective Y] (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k] (K.homology (-i) ⟶ Y) :=
  LinearEquiv.ofBijective _ (linearHomComplexSingleKronecker_bijective K Y i)

/-- The equivalence `CochainComplex.linearHomComplexSingleKroneckerEquiv` is the Kronecker map. -/
@[simp]
lemma linearHomComplexSingleKroneckerEquiv_apply [Injective Y] (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    linearHomComplexSingleKroneckerEquiv k K Y i x = linearHomComplexSingleKronecker k K Y i x :=
  (rfl)

/-- If the inclusion of the cocycles of `K` in degree `-i` is a split monomorphism, then every
morphism `H⁻ⁱ(K) ⟶ Y` is the evaluation of a cohomology class of `Hom(K, Y[0])` of degree `i`. -/
theorem linearHomComplexSingleKronecker_surjective (i : ℤ) [IsSplitMono (K.iCycles (-i))] :
    Function.Surjective (linearHomComplexSingleKronecker k K Y i) := by
  have := K.isSplitMono_restrictionDownIntUpInt_iCycles i (-i) (add_neg_cancel i)
  rw [linearHomComplexSingleKronecker, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (LinearEquiv.surjective _).comp
    ((TauCeti.ChainComplex.kronecker_surjective_of_isSplitMono i).comp (LinearEquiv.surjective _))

end Ring

/-! ### The `Ext` term of the universal coefficient sequence -/

section Ext

universe w

variable {k : Type*} [CommRing k] [Linear k C] [HasExt.{w} C] (K : CochainComplex C ℤ) (Y : C)

/-! The universal coefficient sequence of `K⁻` in degree `i` involves its cycles in degree `i - 1`,
which are those of `K` in degree `1 - i`. The two transfers below are local instances, so that the
hypotheses on `K` in degree `1 - i` supply the instances that the chain-complex `Ext¹` map of `K⁻`
needs. -/

omit [HasExt.{w} C] in
/-- The cycles of `K⁻` in degree `i - 1` are projective when those of `K` in degree `1 - i` are. -/
private lemma projective_restrictionDownIntUpInt_cycles_sub_one (i : ℤ)
    [Projective (K.cycles (1 - i))] :
    Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).cycles (i - 1)) :=
  K.projective_restrictionDownIntUpInt_cycles (i - 1) (1 - i) (by omega)

omit [HasExt.{w} C] in
/-- The cycles of `K⁻` in degree `i - 1` split off when those of `K` in degree `1 - i` do. -/
private lemma isSplitMono_restrictionDownIntUpInt_iCycles_sub_one (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] :
    IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles (i - 1)) :=
  K.isSplitMono_restrictionDownIntUpInt_iCycles (i - 1) (1 - i) (by omega)

attribute [local instance] projective_restrictionDownIntUpInt_cycles_sub_one
  isSplitMono_restrictionDownIntUpInt_iCycles_sub_one

variable (k) in
/-- **The `Ext` term of the universal coefficient sequence** of the Hom complex into `Y[0]`: the
`k`-linear map `Ext¹(H¹⁻ⁱ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))`, defined when the cocycles of `K` in
degree `1 - i` are projective and split off `K¹⁻ⁱ`. It is the map
`TauCeti.ChainComplex.extToHomology` of the chain complex `K⁻` with `K⁻ᵢ = K⁻ⁱ`, transported along
`CochainComplex.linearHomComplexSingleIso` and the identification of the homology of `K⁻` in
degree `i - 1` with `H¹⁻ⁱ(K)`. -/
def linearHomComplexSingleExtToHomology (i : ℤ) [Projective (K.cycles (1 - i))]
    [IsSplitMono (K.iCycles (1 - i))] :
    Ext.{w} (K.homology (1 - i)) Y 1 →ₗ[k]
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i :=
  (homSingleHomologyEquiv k K Y i).symm.toLinearMap ∘ₗ
    TauCeti.ChainComplex.extToHomology k _ Y i (i - 1) ∘ₗ
      (TauCeti.extLinearEquivOfIso k
        (K.restrictionDownIntUpIntHomologyIso (i - 1) (1 - i) (by omega)).symm (Iso.refl Y)
        1).toLinearMap

omit [HasExt.{w} C] in
/-- The coboundaries of `K` in degree `1 - i`, read on `K⁻`: the corestriction of the differential
`K⁻ⁱ ⟶ B¹⁻ⁱ` of `K` is that of `K⁻` followed by the identification of the boundaries. -/
@[reassoc]
private lemma restrictionXIso_inv_toBoundaries_kernelMap (i : ℤ) :
    (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
        (ComplexShape.embeddingDownIntUpInt_f i)).inv ≫
      (K.restriction ComplexShape.embeddingDownIntUpInt).toBoundaries i (i - 1) ≫
        kernel.map _ _ (K.restrictionDownIntUpIntCyclesIso (i - 1) (1 - i) (by omega)).hom
          (K.restrictionDownIntUpIntHomologyIso (i - 1) (1 - i) (by omega)).hom
          (homologyπ_restrictionDownIntUpIntHomologyIso_hom ..) =
      K.toBoundaries (-i) (1 - i) := by
  rw [← cancel_mono (kernel.ι _), ← cancel_mono (K.iCycles _)]
  simp [-restriction_d, restriction_d_eq K ComplexShape.embeddingDownIntUpInt (i' := -i)
    (j' := 1 - i) (ComplexShape.embeddingDownIntUpInt_f i)
    (show ComplexShape.embeddingDownIntUpInt.f (i - 1) = 1 - i by simp)]

/-- **The characterization of `CochainComplex.linearHomComplexSingleExtToHomology`**: the class in
`Ext¹(H¹⁻ⁱ(K), Y)` of a morphism `β : B¹⁻ⁱ ⟶ Y` from the coboundaries of `K` goes to the class of
a cocycle `φ` of `Hom(K, Y[0])` of degree `i` whose underlying morphism `K⁻ⁱ ⟶ Y` is
`K⁻ⁱ ⟶ B¹⁻ⁱ ⟶ Y`. -/
lemma linearHomComplexSingleExtToHomology_extClass_comp_mk₀ (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    (β : kernel (K.homologyπ (1 - i)) ⟶ Y)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (hφ : Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) =
      K.toBoundaries (-i) (1 - i) ≫ β) :
    linearHomComplexSingleExtToHomology.{w} k K Y i
        ((TauCeti.kernelSequence_shortExact (K.homologyπ (1 - i))).extClass.comp (Ext.mk₀ β)
          (add_zero 1)) =
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ := by
  let b := kernel.map _ _ (K.restrictionDownIntUpIntCyclesIso (i - 1) (1 - i) (by omega)).hom
    (K.restrictionDownIntUpIntHomologyIso (i - 1) (1 - i) (by omega)).hom
    (homologyπ_restrictionDownIntUpIntHomologyIso_hom ..)
  -- state the kernel sequences with explicit terms, so that rewriting sees their objects
  have hK : (ShortComplex.mk (kernel.ι (K.homologyπ (1 - i))) _ (kernel.condition _)).ShortExact :=
    TauCeti.kernelSequence_shortExact _
  have hL : (ShortComplex.mk (kernel.ι ((K.restriction ComplexShape.embeddingDownIntUpInt).homologyπ
      (i - 1))) _ (kernel.condition _)).ShortExact := TauCeti.kernelSequence_shortExact _
  -- the extension classes of the kernel sequences of `K⁻` and `K` correspond
  have hn := ShortComplex.ShortExact.extClass_naturality hL hK
    { τ₁ := b
      τ₂ := (K.restrictionDownIntUpIntCyclesIso (i - 1) (1 - i) (by omega)).hom
      τ₃ := (K.restrictionDownIntUpIntHomologyIso (i - 1) (1 - i) (by omega)).hom
      comm₁₂ := kernel.lift_ι _ _ _
      comm₂₃ := (homologyπ_restrictionDownIntUpIntHomologyIso_hom ..).symm }
  have he : TauCeti.extLinearEquivOfIso k
      (K.restrictionDownIntUpIntHomologyIso (i - 1) (1 - i) (by omega)).symm (Iso.refl Y) 1
      (hK.extClass.comp (Ext.mk₀ β) (add_zero 1)) =
      hL.extClass.comp (Ext.mk₀ (b ≫ β)) (add_zero 1) := by
    rw [TauCeti.extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id,
      ← Ext.comp_assoc_of_third_deg_zero, ← hn, Ext.comp_assoc_of_second_deg_zero,
      Ext.mk₀_comp_mk₀]
  have hψ : (ChainComplex.linearYonedaObj _ k Y).iCycles i
      (homSingleSign i • cyclesMap (linearHomComplexSingleIso k K Y).hom i φ) =
        (K.restriction ComplexShape.embeddingDownIntUpInt).toBoundaries i (i - 1) ≫ b ≫ β := by
    rw [iCycles_homSingleSign_smul_cyclesMap]
    exact (cancel_epi (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
        (ComplexShape.embeddingDownIntUpInt_f i)).inv).1
      ((HomComplex.Cochain.restrictionXIso_inv_comp_toSingleEquiv _ _ _ _ (neg_add_cancel i) _
        _).trans (hφ.trans (restrictionXIso_inv_toBoundaries_kernelMap_assoc K i β).symm))
  exact (LinearEquiv.symm_apply_eq _).2 ((congrArg (TauCeti.ChainComplex.extToHomology k _ Y i
    (i - 1)) he).trans ((TauCeti.ChainComplex.extToHomology_extClass_comp_mk₀ i (i - 1) (b ≫ β)
      _ hψ).trans (homSingleHomologyEquiv_homologyπ K Y i φ).symm))

/-- **Injectivity in the universal coefficient sequence** of the Hom complex into `Y[0]`: the map
`Ext¹(H¹⁻ⁱ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))` is injective. -/
theorem linearHomComplexSingleExtToHomology_injective (i : ℤ) [Projective (K.cycles (1 - i))]
    [IsSplitMono (K.iCycles (1 - i))] :
    Function.Injective (linearHomComplexSingleExtToHomology.{w} k K Y i) := by
  rw [linearHomComplexSingleExtToHomology, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (LinearEquiv.injective _).comp
    ((TauCeti.ChainComplex.extToHomology_injective (sub_add_cancel i 1)).comp
      (LinearEquiv.injective _))

/-- **Exactness in the middle of the universal coefficient sequence** of the Hom complex into
`Y[0]`: a cohomology class of `Hom(K, Y[0])` of degree `i` evaluates to zero on `H⁻ⁱ(K)` exactly
when it comes from `Ext¹(H¹⁻ⁱ(K), Y)`. -/
theorem exact_linearHomComplexSingleExtToHomology_linearHomComplexSingleKronecker (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))] :
    Function.Exact (linearHomComplexSingleExtToHomology.{w} k K Y i)
      (linearHomComplexSingleKronecker k K Y i) := by
  rw [linearHomComplexSingleExtToHomology, linearHomComplexSingleKronecker,
    LinearEquiv.postcomp_exact_iff_exact, LinearEquiv.conj_symm_exact_iff_exact,
    LinearEquiv.precomp_exact_iff_exact]
  exact TauCeti.ChainComplex.exact_extToHomology_kronecker (sub_add_cancel i 1)

end Ext

end CochainComplex
