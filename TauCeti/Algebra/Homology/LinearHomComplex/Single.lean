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
public import TauCeti.Algebra.Homology.LinearHomComplex.Basic
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Algebra.Homology.UniversalCoefficient.Basic
public import TauCeti.Algebra.Homology.UniversalCoefficient.Naturality
public import TauCeti.Algebra.Ring.NegOnePow

/-!
# The Hom complex into an object placed in degree zero

Let `K` be a cochain complex indexed by `ℤ` in a `k`-linear abelian category `C`, and let `Y : C`.
The `k`-linear Hom complex `Hom(K, Y[0])` (`CochainComplex.linearHomComplex`) into the complex `Y`
concentrated in degree zero is the dual complex of `K` with coefficients in `Y`: in degree `i` its
term is the module of morphisms `K⁻ⁱ ⟶ Y` (`HomComplex.Cochain.toSingleEquiv`), and its
differential is `f ↦ (-1)^(i+1) f ∘ d`
(`CochainComplex.toSingleLinearEquiv_linearHomComplex_d_apply`). For `C = ModuleCat R` and `Y = R`
this is the dual of a complex of `R`-modules, reversing cochain degrees.

Reading `K` as the chain complex `K⁻` with `K⁻ᵢ = K⁻ⁱ` (the restriction along `n ↦ -n`, as in
Mathlib's `ChainComplex.cochainComplexEquivalence`), the dual complex is isomorphic to the linear
Yoneda complex `Hom(K⁻, Y)` (`ChainComplex.linearYonedaObj`), whose differential has no sign. The
isomorphism `CochainComplex.linearHomComplexSingleIso` multiplies by `(-1)^(i(i+1)/2)` in degree
`i` and is natural in both `K` and `Y`. Through it, the Kronecker map and the universal coefficient
sequence of chain complexes (`TauCeti.Algebra.Homology.Kronecker` and
`TauCeti.Algebra.Homology.UniversalCoefficient.Basic`) give the universal coefficient sequence of
the dual complex,

`0 ⟶ Ext¹(H¹⁻ⁱ(K), Y) ⟶ Hⁱ(Hom(K, Y[0])) ⟶ (H⁻ⁱ(K) ⟶ Y) ⟶ 0`,

exact when the cocycles of `K` in degrees `1 - i` and `-i` split off and those in degree `1 - i`
are projective, for instance for a complex of free abelian groups, with non-canonical splitting
`CochainComplex.linearHomComplexSingleUniversalCoefficientEquiv` induced by a chosen retraction of
`K.iCycles (-i)` (`CochainComplex.linearHomComplexSingleKroneckerSection`). Both arrows in the
sequence are natural in `K` and `Y`, and the splitting commutes with morphisms in `Y`. For an
injective object `Y`, such as a field over itself, or when `H¹⁻ⁱ(K)` is projective and the cocycles
in degrees `1 - i` and `-i` split off, the Kronecker map is an isomorphism. The sign is corrected in
the Kronecker map `CochainComplex.linearHomComplexSingleKronecker`, which evaluates a cocycle on
cocycles of `K` without any sign (`CochainComplex.homologyπ_linearHomComplexSingleKronecker`).

## Main definitions and results

* `CochainComplex.linearHomComplexSingleIso` and
  `CochainComplex.linearHomComplexSingleHomologyEquiv`: the isomorphism `Hom(K, Y[0]) ≅ Hom(K⁻, Y)`
  and its sign-corrected `k`-linear cohomology equivalence, both natural in `K` and `Y`. The cycles
  and homology of `K⁻` are compared with those of `K` by
  `CochainComplex.restrictionDownIntUpIntCyclesIso` and
  `CochainComplex.restrictionDownIntUpIntHomologyIso`.
* `CochainComplex.linearHomComplexSingleKronecker`: the Kronecker map
  `Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)`, characterized by
  `CochainComplex.homologyπ_linearHomComplexSingleKronecker`, with right inverse
  `CochainComplex.linearHomComplexSingleKroneckerSection` when `K.iCycles (-i)` splits.
* `CochainComplex.linearHomComplexSingleKronecker_bijective`,
  `CochainComplex.linearHomComplexSingleKroneckerEquiv`, and
  `CochainComplex.linearHomComplexSingleKroneckerEquivOfProjectiveHomology`: the Kronecker map is a
  `k`-linear equivalence when `Y` is injective or when `H¹⁻ⁱ(K)` is projective and the cocycles in
  degrees `1 - i` and `-i` split off.
* `CochainComplex.linearHomComplexSingleKronecker_surjective`: it is surjective when the cocycles
  of `K` split off in degree `-i`.
* `CochainComplex.linearHomComplexSingleExtToHomology` (characterized by
  `CochainComplex.linearHomComplexSingleExtToHomology_extClass_comp_mk₀`),
  `CochainComplex.linearHomComplexSingleExtToHomology_injective`,
  `CochainComplex.exact_linearHomComplexSingleExtToHomology_linearHomComplexSingleKronecker`, and
  `CochainComplex.linearHomComplexSingleUniversalCoefficientEquiv`: the `Ext¹` term of the universal
  coefficient sequence, exactness at its first two places, and the resulting split decomposition.

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

/-- Under `Cochain.toSingleLinearEquiv`, the differential `i → i + 1` of
`linearHomComplex k K ((singleFunctor C 0).obj Y)` sends `f : K⁻ⁱ ⟶ Y` to
`(-1) ^ (i + 1) • (K.d (-(i + 1)) (-i) ≫ f)`. -/
lemma toSingleLinearEquiv_linearHomComplex_d_apply (k : Type*) [Ring k] [Linear k C] (i : ℤ)
    (z : (linearHomComplex k K ((singleFunctor C 0).obj Y)).X i) :
    Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel (i + 1))
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).d i (i + 1)).hom z) =
      ((i + 1).negOnePow : ℤ) •
        (K.d (-(i + 1)) (-i) ≫ Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z) := by
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-i) (neg_add_cancel i)
  -- `linearHomComplex_d_hom_apply` is stated on the unfolded carrier `Cochain K _ i`.
  erw [linearHomComplex_d_hom_apply]
  simp only [Cochain.toSingleLinearEquiv_apply, AddEquiv.toFun_eq_coe,
    Cochain.toSingleEquiv_toSingleMk,
    Cochain.δ_toSingleMk f (neg_add_cancel i) (i + 1) (-(i + 1)) (neg_add_cancel (i + 1)),
    Units.smul_def, map_zsmul]

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

variable {Y} in
/-- `CochainComplex.linearHomComplexSingleIso` commutes with postcomposition by a coefficient
morphism `g : Y ⟶ Z`. -/
@[reassoc]
lemma linearHomComplexPostcomp_comp_linearHomComplexSingleIso_hom {Z : C} (g : Y ⟶ Z) :
    TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g) ≫
        (linearHomComplexSingleIso k K Z).hom =
      (linearHomComplexSingleIso k K Y).hom ≫
        ChainComplex.linearYonedaObjMap k
          (K.restriction ComplexShape.embeddingDownIntUpInt) g := by
  ext i z
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-i) (neg_add_cancel i)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  -- Component lemmas are stated on the unfolded carriers of `linearHomComplex` and
  -- `linearYonedaObj`.
  erw [ChainComplex.linearYonedaObjMap_f_hom_apply, linearHomComplexSingleIso_hom_f_apply,
    linearHomComplexSingleIso_hom_f_apply, TauCeti.linearHomComplexPostcomp_f_apply]
  rw [← Cochain.toSingleMk_postcomp, Cochain.toSingleEquiv_toSingleMk,
    Cochain.toSingleEquiv_toSingleMk, Units.smul_def, Units.smul_def]
  exact (Preadditive.zsmul_comp f g _).symm

variable {K} in
/-- `CochainComplex.linearHomComplexSingleIso` commutes with precomposition by a cochain map
`φ : K' ⟶ K`. -/
@[reassoc]
lemma linearHomComplexPrecomp_comp_linearHomComplexSingleIso_hom
    {K' : CochainComplex C ℤ} (φ : K' ⟶ K) :
    TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y) ≫
        (linearHomComplexSingleIso k K' Y).hom =
      (linearHomComplexSingleIso k K Y).hom ≫
        (TauCeti.ChainComplex.linearYonedaFunctor k Y).map
          (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op := by
  ext i z
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-i) (neg_add_cancel i)
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  -- `(linearYonedaFunctor k Y).obj (op _)` unfolds to `(restriction _).linearYonedaObj k Y`.
  erw [HomologicalComplex.comp_f, ModuleCat.hom_comp]
  rw [LinearMap.comp_apply]
  erw [TauCeti.ChainComplex.linearYonedaFunctor_map_f_hom_apply,
    linearHomComplexSingleIso_hom_f_apply, linearHomComplexSingleIso_hom_f_apply,
    TauCeti.linearHomComplexPrecomp_f_apply]
  rw [Quiver.Hom.unop_op, HomologicalComplex.restrictionMap_f,
    ← Cochain.toSingleMk_precomp, Cochain.toSingleEquiv_toSingleMk,
    Cochain.toSingleEquiv_toSingleMk, Units.smul_def, Units.smul_def]
  exact (Preadditive.comp_zsmul _ f _).symm

/-! ### The Kronecker map -/

variable (k) in
/-- **The sign-corrected cohomology equivalence** between the Hom complex `Hom(K, Y[0])` and the
linear Yoneda complex `Hom(K⁻, Y)` in degree `i`: the equivalence induced by
`CochainComplex.linearHomComplexSingleIso` twisted by `(-1)^(i(i+1)/2)`, so that cocycles
corresponding under `HomComplex.Cochain.toSingleEquiv` correspond without sign
(`CochainComplex.linearHomComplexSingleHomologyEquiv_homologyπ_eq`). -/
def linearHomComplexSingleHomologyEquiv (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k]
      (ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k
        Y).homology i :=
  ((homologyFunctor _ _ i).mapIso (linearHomComplexSingleIso k K Y)).toLinearEquiv.trans
    (DistribMulAction.toLinearEquiv k _ (homSingleSign i))

/-- `CochainComplex.linearHomComplexSingleHomologyEquiv` acts as `(-1)^(i(i+1)/2)` times the map on
cohomology induced by `CochainComplex.linearHomComplexSingleIso`. -/
lemma linearHomComplexSingleHomologyEquiv_apply (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    linearHomComplexSingleHomologyEquiv k K Y i x =
      (i * (i + 1) / 2).negOnePow •
        homologyMap (linearHomComplexSingleIso k K Y).hom i x :=
  (rfl)

/-- The inverse of `CochainComplex.linearHomComplexSingleHomologyEquiv` acts as `(-1)^(i(i+1)/2)`
times the map on homology induced by the inverse of `CochainComplex.linearHomComplexSingleIso`. -/
lemma linearHomComplexSingleHomologyEquiv_symm_apply (i : ℤ)
    (x : (ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k
      Y).homology i) :
    (linearHomComplexSingleHomologyEquiv k K Y i).symm x =
      (i * (i + 1) / 2).negOnePow •
        homologyMap (linearHomComplexSingleIso k K Y).inv i x := by
  simp [linearHomComplexSingleHomologyEquiv, homSingleSign, Int.units_inv_eq_self, Units.smul_def]

/-- `CochainComplex.linearHomComplexSingleHomologyEquiv` sends the class of a cocycle `φ` of
`Hom(K, Y[0])` to the class of
`(-1)^(i(i+1)/2) • cyclesMap (linearHomComplexSingleIso k K Y).hom i φ`, cancelling the sign of
`CochainComplex.linearHomComplexSingleIso`. -/
@[simp]
lemma linearHomComplexSingleHomologyEquiv_homologyπ (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i) :
    linearHomComplexSingleHomologyEquiv k K Y i
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ) =
      (ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k
        Y).homologyπ i
        ((i * (i + 1) / 2).negOnePow • cyclesMap (linearHomComplexSingleIso k K Y).hom i φ) := by
  simp [linearHomComplexSingleHomologyEquiv, homSingleSign, moduleCat_homologyMap_homologyπ]

/-- The cocycle of `Hom(K⁻, Y)` of `CochainComplex.linearHomComplexSingleHomologyEquiv_homologyπ`
has the same underlying morphism `K⁻ⁱ ⟶ Y` as `φ`. -/
private lemma iCycles_homSingleSign_smul_cyclesMap (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i) :
    (ChainComplex.linearYonedaObj _ k Y).iCycles i
        (homSingleSign i • cyclesMap (linearHomComplexSingleIso k K Y).hom i φ) =
      Cochain.toSingleEquiv (embeddingDownIntUpInt_f_add_self i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) := by
  rw [Units.smul_def, map_zsmul, moduleCat_iCycles_cyclesMap_apply, ← Units.smul_def]
  exact Int.negOnePow_smul_negOnePow_smul _ _

/-- `CochainComplex.linearHomComplexSingleHomologyEquiv` sends the class of a cocycle `φ` of
`Hom(K, Y[0])` to the class of any cocycle `ψ` of `Hom(K⁻, Y)` with the same underlying morphism
`K⁻ⁱ ⟶ Y`, without sign. -/
lemma linearHomComplexSingleHomologyEquiv_homologyπ_eq (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (ψ : (ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).cycles i)
    (hψ : (ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).iCycles i ψ =
      Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ)) :
    linearHomComplexSingleHomologyEquiv k K Y i
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ) =
      (ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homologyπ i ψ := by
  rw [linearHomComplexSingleHomologyEquiv_homologyπ]
  congr 1
  exact moduleCat_iCycles_injective _ i
    ((iCycles_homSingleSign_smul_cyclesMap K Y i φ).trans hψ.symm)

variable {Y} in
/-- `CochainComplex.linearHomComplexSingleHomologyEquiv` commutes with postcomposition by a
coefficient morphism `g : Y ⟶ Z`. -/
lemma linearHomComplexSingleHomologyEquiv_postcomp {Z : C} (g : Y ⟶ Z) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    linearHomComplexSingleHomologyEquiv k K Z i
        (homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i x) =
      homologyMap (ChainComplex.linearYonedaObjMap k
        (K.restriction ComplexShape.embeddingDownIntUpInt) g) i
        (linearHomComplexSingleHomologyEquiv k K Y i x) := by
  simp only [linearHomComplexSingleHomologyEquiv, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply,
    Functor.mapIso_hom, homologyFunctor_map, DistribMulAction.toLinearEquiv_apply,
    Units.smul_def, map_zsmul, ← ModuleCat.comp_apply, ← homologyMap_comp,
    linearHomComplexPostcomp_comp_linearHomComplexSingleIso_hom K g]

variable {K} in
/-- `CochainComplex.linearHomComplexSingleHomologyEquiv` commutes with precomposition by a cochain
map `φ : K' ⟶ K`. -/
lemma linearHomComplexSingleHomologyEquiv_precomp {K' : CochainComplex C ℤ} (φ : K' ⟶ K) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    linearHomComplexSingleHomologyEquiv k K' Y i
        (homologyMap (TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i x) =
      homologyMap
        (K := ChainComplex.linearYonedaObj
          (K.restriction ComplexShape.embeddingDownIntUpInt) k Y)
        (L := ChainComplex.linearYonedaObj
          (K'.restriction ComplexShape.embeddingDownIntUpInt) k Y)
        ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map
          (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op) i
        (linearHomComplexSingleHomologyEquiv k K Y i x) := by
  let ψ : ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y ⟶
      ChainComplex.linearYonedaObj
        (K'.restriction ComplexShape.embeddingDownIntUpInt) k Y :=
    (TauCeti.ChainComplex.linearYonedaFunctor k Y).map
      (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op
  have hcomm : TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y) ≫
      (linearHomComplexSingleIso k K' Y).hom =
      (linearHomComplexSingleIso k K Y).hom ≫ ψ :=
    linearHomComplexPrecomp_comp_linearHomComplexSingleIso_hom Y φ
  have hhom : homologyMap (TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i ≫
      homologyMap (linearHomComplexSingleIso k K' Y).hom i =
      homologyMap (linearHomComplexSingleIso k K Y).hom i ≫ homologyMap ψ i := by
    rw [← homologyMap_comp, ← homologyMap_comp, hcomm]
  simp only [linearHomComplexSingleHomologyEquiv, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply,
    Functor.mapIso_hom, homologyFunctor_map, DistribMulAction.toLinearEquiv_apply,
    Units.smul_def, map_zsmul, ← ModuleCat.comp_apply]
  exact congrArg (((homSingleSign i : ℤ) • ·)) (congrArg (fun f ↦ f x) hhom)

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
    TauCeti.ChainComplex.kronecker k _ Y i ∘ₗ
      (linearHomComplexSingleHomologyEquiv k K Y i).toLinearMap

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
    Function.comp_apply, linearHomComplexSingleHomologyEquiv_homologyπ, homSingleSign,
    map_zsmul_unit, Linear.homCongr_apply, Iso.refl_hom, Category.comp_id, Linear.comp_units_smul,
    homologyπ_restrictionDownIntUpIntHomologyIso_inv_assoc,
    TauCeti.ChainComplex.kronecker_homologyπ, restriction_X, ComplexShape.embeddingDownIntUpInt_f,
    moduleCat_iCycles_cyclesMap_apply, linearHomComplexSingleIso_hom_f_apply_restriction,
    restrictionDownIntUpIntCyclesIso_inv_iCycles_assoc,
    Int.negOnePow_smul_negOnePow_smul]
  rw [HomComplex.Cochain.restrictionXIso_inv_comp_toSingleEquiv]

variable {K} in
/-- **Naturality of the Kronecker map** in the source cochain complex `K`. -/
lemma linearHomComplexSingleKronecker_naturality {K' : CochainComplex C ℤ} (φ : K' ⟶ K) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    linearHomComplexSingleKronecker k K' Y i
        (homologyMap (TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i x) =
      homologyMap φ (-i) ≫ linearHomComplexSingleKronecker k K Y i x := by
  have hinv := homologyMap_restrictionDownIntUpIntHomologyIso_inv φ i (-i) (add_neg_cancel i)
  simp only [linearHomComplexSingleKronecker, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Linear.homCongr_apply, Iso.refl_hom, Category.comp_id,
    linearHomComplexSingleHomologyEquiv_precomp, TauCeti.ChainComplex.kronecker_naturality,
    ← reassoc_of% hinv]

variable {Y} in
/-- **Coefficient naturality of the Kronecker map** in `Y`. -/
lemma linearHomComplexSingleKronecker_coefficient_naturality {Z : C} (g : Y ⟶ Z) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    linearHomComplexSingleKronecker k K Z i
        (homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i x) =
      linearHomComplexSingleKronecker k K Y i x ≫ g := by
  simp only [linearHomComplexSingleKronecker, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Linear.homCongr_apply, Iso.refl_hom, Category.comp_id,
    linearHomComplexSingleHomologyEquiv_postcomp,
    TauCeti.ChainComplex.kronecker_coefficient_naturality, Category.assoc]

/-- **The universal coefficient theorem for injective coefficients**: for an injective object
`Y`, the Kronecker map `Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)` is bijective. -/
theorem linearHomComplexSingleKronecker_bijective [Injective Y] (i : ℤ) :
    Function.Bijective (linearHomComplexSingleKronecker k K Y i) := by
  rw [linearHomComplexSingleKronecker, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (LinearEquiv.bijective _).comp ((TauCeti.ChainComplex.kronecker_bijective i).comp
    (LinearEquiv.bijective _))

variable (k) in
/-- `CochainComplex.linearHomComplexSingleKronecker` as a `k`-linear equivalence, for an
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

/-- The cycles of `K⁻` in degree `i` split off when those of `K` in degree `-i` do. -/
private lemma isSplitMono_restrictionDownIntUpInt_iCycles_self (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] :
    IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles i) :=
  K.isSplitMono_restrictionDownIntUpInt_iCycles i (-i) (add_neg_cancel i)

attribute [local instance] isSplitMono_restrictionDownIntUpInt_iCycles_self

private lemma restriction_d_retraction_iCycles_comp_homologyπ (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] :
    (K.restriction ComplexShape.embeddingDownIntUpInt).d ((ComplexShape.up ℤ).next i) i ≫
      (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
        (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫
      retraction (K.iCycles (-i)) ≫ K.homologyπ (-i) = 0 := by
  rw [HomologicalComplex.restriction_d_eq_assoc K ComplexShape.embeddingDownIntUpInt
    (ComplexShape.embeddingDownIntUpInt_f ((ComplexShape.up ℤ).next i))
    (ComplexShape.embeddingDownIntUpInt_f i),
    Iso.inv_hom_id_assoc, ← K.toCycles_i_assoc, IsSplitMono.id_assoc,
    toCycles_comp_homologyπ, comp_zero]

variable (k) in
/-- **A `k`-linear section of the Kronecker map**: when `K.iCycles (-i)` is a split monomorphism,
the right inverse `(H⁻ⁱ(K) ⟶ Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))` of
`CochainComplex.linearHomComplexSingleKronecker` sending `g` to the cocycle class induced by
`retraction (K.iCycles (-i))` (`CochainComplex.linearHomComplexSingleKroneckerSection_apply`). -/
def linearHomComplexSingleKroneckerSection (i : ℤ) [IsSplitMono (K.iCycles (-i))] :
    (K.homology (-i) ⟶ Y) →ₗ[k]
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i :=
  (linearHomComplexSingleHomologyEquiv k K Y i).symm.toLinearMap ∘ₗ
    TauCeti.ChainComplex.homologyClassOfComp k Y
      (X := K.restriction ComplexShape.embeddingDownIntUpInt)
      ((K.restrictionXIso ComplexShape.embeddingDownIntUpInt
          (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫
        retraction (K.iCycles (-i)) ≫ K.homologyπ (-i))
      (restriction_d_retraction_iCycles_comp_homologyπ K i)

/-- `CochainComplex.linearHomComplexSingleKroneckerSection` is a right inverse of
`CochainComplex.linearHomComplexSingleKronecker`. -/
@[simp]
lemma linearHomComplexSingleKronecker_linearHomComplexSingleKroneckerSection (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] (g : K.homology (-i) ⟶ Y) :
    linearHomComplexSingleKronecker k K Y i
        (linearHomComplexSingleKroneckerSection k K Y i g) = g := by
  rw [← cancel_epi (K.homologyπ (-i))]
  simp only [linearHomComplexSingleKronecker, linearHomComplexSingleKroneckerSection,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    Linear.homCongr_apply, Iso.refl_hom, Category.comp_id]
  rw [homologyπ_restrictionDownIntUpIntHomologyIso_inv_assoc,
    TauCeti.ChainComplex.homologyπ_kronecker_homologyClassOfComp,
    restrictionDownIntUpIntCyclesIso_inv_iCycles_assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, IsSplitMono.id_assoc]

/-- **`CochainComplex.linearHomComplexSingleKroneckerSection` on cocycle representatives**:
`linearHomComplexSingleKroneckerSection k K Y i g` is the class of any cocycle `φ` whose underlying
morphism `K⁻ⁱ ⟶ Y` is `retraction (K.iCycles (-i)) ≫ K.homologyπ (-i) ≫ g`. -/
lemma linearHomComplexSingleKroneckerSection_apply (i : ℤ) [IsSplitMono (K.iCycles (-i))]
    (g : K.homology (-i) ⟶ Y)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (hφ : Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) =
      retraction (K.iCycles (-i)) ≫ K.homologyπ (-i) ≫ g) :
    linearHomComplexSingleKroneckerSection k K Y i g =
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ := by
  have hψ : (ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k
        Y).iCycles i (homSingleSign i • cyclesMap (linearHomComplexSingleIso k K Y).hom i φ) =
      ((K.restrictionXIso ComplexShape.embeddingDownIntUpInt
          (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫
        retraction (K.iCycles (-i)) ≫ K.homologyπ (-i)) ≫ g := by
    rw [iCycles_homSingleSign_smul_cyclesMap]
    exact (cancel_epi (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
        (ComplexShape.embeddingDownIntUpInt_f i)).inv).1
      ((HomComplex.Cochain.restrictionXIso_inv_comp_toSingleEquiv _ _ _ _ (neg_add_cancel i) _
        _).trans (hφ.trans (by simp)))
  exact (LinearEquiv.symm_apply_eq _).2
    ((TauCeti.ChainComplex.homologyClassOfComp_eq _ _ g _ hψ).trans
      (linearHomComplexSingleHomologyEquiv_homologyπ K Y i φ).symm)

variable {Y} in
/-- `CochainComplex.linearHomComplexSingleKroneckerSection` commutes with postcomposition by a
coefficient morphism `g : Y ⟶ Z`, for the same chosen retraction of `K.iCycles (-i)`. -/
lemma linearHomComplexSingleKroneckerSection_coefficient_naturality {Z : C} (g : Y ⟶ Z) (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] (f : K.homology (-i) ⟶ Y) :
    homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i
        (linearHomComplexSingleKroneckerSection k K Y i f) =
      linearHomComplexSingleKroneckerSection k K Z i (f ≫ g) := by
  let X : ChainComplex C ℤ := K.restriction ComplexShape.embeddingDownIntUpInt
  have hf := restriction_d_retraction_iCycles_comp_homologyπ K i
  let ψ := TauCeti.ChainComplex.cocycleOfComp k Y (X := X) _ hf f
  have hψ := TauCeti.ChainComplex.iCycles_cocycleOfComp (k := k) (Y := Y) (X := X) _ hf f
  apply (linearHomComplexSingleHomologyEquiv k K Z i).injective
  rw [linearHomComplexSingleHomologyEquiv_postcomp]
  simp only [linearHomComplexSingleKroneckerSection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rw [TauCeti.ChainComplex.homologyClassOfComp_eq _ hf f ψ hψ,
    X.homologyMap_linearYonedaObjMap_homologyπ_apply k]
  exact (TauCeti.ChainComplex.homologyClassOfComp_eq _ hf (f ≫ g) _
    ((X.iCycles_cyclesMap_linearYonedaObjMap_apply k g i ψ).trans
      (by rw [hψ, Category.assoc]))).symm

/-- If the inclusion of the cocycles of `K` in degree `-i` is a split monomorphism, then every
morphism `H⁻ⁱ(K) ⟶ Y` is the evaluation of a cohomology class of `Hom(K, Y[0])` of degree `i`. -/
theorem linearHomComplexSingleKronecker_surjective (i : ℤ) [IsSplitMono (K.iCycles (-i))] :
    Function.Surjective (linearHomComplexSingleKronecker k K Y i) := by
  rw [linearHomComplexSingleKronecker, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (LinearEquiv.surjective _).comp
    ((TauCeti.ChainComplex.kronecker_surjective_of_isSplitMono i).comp (LinearEquiv.surjective _))

/-- **The universal coefficient theorem with projective `(1 - i)`-th cohomology**: when
`K.iCycles (1 - i)` and `K.iCycles (-i)` split and `K.homology (1 - i)` is projective, the
Kronecker map `Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)` is bijective over any ring `k`. -/
theorem linearHomComplexSingleKronecker_bijective_of_projective_homology (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] [IsSplitMono (K.iCycles (-i))]
    [Projective (K.homology (1 - i))] :
    Function.Bijective (linearHomComplexSingleKronecker k K Y i) := by
  have := K.isSplitMono_restrictionDownIntUpInt_iCycles (i - 1) (1 - i) (by omega)
  have := K.projective_restrictionDownIntUpInt_homology (i - 1) (1 - i) (by omega)
  rw [linearHomComplexSingleKronecker, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (LinearEquiv.bijective _).comp
    ((TauCeti.ChainComplex.kronecker_bijective_of_projective_homology_of_add_one_eq
      (sub_add_cancel i 1)).comp (LinearEquiv.bijective _))

variable (k) in
/-- When `K.iCycles (1 - i)` and `K.iCycles (-i)` split and `K.homology (1 - i)` is projective,
the Kronecker map as a `k`-linear equivalence `Hⁱ(Hom(K, Y[0])) ≃ₗ[k] (H⁻ⁱ(K) ⟶ Y)`. -/
def linearHomComplexSingleKroneckerEquivOfProjectiveHomology (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] [IsSplitMono (K.iCycles (-i))]
    [Projective (K.homology (1 - i))] :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k] (K.homology (-i) ⟶ Y) :=
  LinearEquiv.ofBijective _
    (linearHomComplexSingleKronecker_bijective_of_projective_homology K Y i)

@[simp]
lemma linearHomComplexSingleKroneckerEquivOfProjectiveHomology_apply (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] [IsSplitMono (K.iCycles (-i))]
    [Projective (K.homology (1 - i))]
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    linearHomComplexSingleKroneckerEquivOfProjectiveHomology k K Y i x =
      linearHomComplexSingleKronecker k K Y i x :=
  (rfl)

/-- If `K.iCycles (1 - i)` and `K.iCycles (-i)` split, `K.homology (1 - i)` is projective, and
`K.homology (-i)` vanishes, then `Hⁱ(Hom(K, Y[0]))` vanishes. -/
theorem isZero_homology_linearHomComplex_single_of_projective_homology (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] [IsSplitMono (K.iCycles (-i))]
    [Projective (K.homology (1 - i))] (hi : IsZero (K.homology (-i))) :
    IsZero ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) := by
  have : Subsingleton (K.homology (-i) ⟶ Y) := ⟨hi.eq_of_src⟩
  have := (linearHomComplexSingleKronecker_bijective_of_projective_homology
    (k := k) K Y i).1.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

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
  isSplitMono_restrictionDownIntUpInt_iCycles_self

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
  (linearHomComplexSingleHomologyEquiv k K Y i).symm.toLinearMap ∘ₗ
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
      _ hψ).trans (linearHomComplexSingleHomologyEquiv_homologyπ K Y i φ).symm))

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

/-- `CochainComplex.linearHomComplexSingleKronecker` vanishes on the image of
`CochainComplex.linearHomComplexSingleExtToHomology`. -/
@[simp]
lemma linearHomComplexSingleKronecker_linearHomComplexSingleExtToHomology (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    (e : Ext.{w} (K.homology (1 - i)) Y 1) :
    linearHomComplexSingleKronecker k K Y i
        (linearHomComplexSingleExtToHomology.{w} k K Y i e) = 0 :=
  (exact_linearHomComplexSingleExtToHomology_linearHomComplexSingleKronecker
    (k := k) K Y i).apply_apply_eq_zero e

variable {K} in
/-- **Naturality of `CochainComplex.linearHomComplexSingleExtToHomology` in `K`**: pulling an
extension back along `homologyMap φ (1 - i)` and including it in cohomology agrees with including
first and pulling back along `φ`. -/
lemma linearHomComplexSingleExtToHomology_naturality {K' : CochainComplex C ℤ} (φ : K' ⟶ K) (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Projective (K'.cycles (1 - i))] [IsSplitMono (K'.iCycles (1 - i))]
    (e : Ext.{w} (K.homology (1 - i)) Y 1) :
    linearHomComplexSingleExtToHomology.{w} k K' Y i
        ((Ext.mk₀ (homologyMap φ (1 - i))).comp e (zero_add 1)) =
      homologyMap (TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i
        (linearHomComplexSingleExtToHomology.{w} k K Y i e) := by
  apply (linearHomComplexSingleHomologyEquiv k K' Y i).injective
  rw [linearHomComplexSingleHomologyEquiv_precomp]
  simp only [linearHomComplexSingleExtToHomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rw [← TauCeti.ChainComplex.extToHomology_naturality]
  congr 1
  simp only [TauCeti.extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id,
    ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1), Ext.mk₀_comp_mk₀,
    homologyMap_restrictionMap_restrictionDownIntUpIntHomologyIso_hom]

variable {Y} in
/-- **Coefficient naturality of `CochainComplex.linearHomComplexSingleExtToHomology` in `Y`**. -/
lemma linearHomComplexSingleExtToHomology_coefficient_naturality {Z : C} (g : Y ⟶ Z) (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    (e : Ext.{w} (K.homology (1 - i)) Y 1) :
    linearHomComplexSingleExtToHomology.{w} k K Z i (e.comp (Ext.mk₀ g) (add_zero 1)) =
      homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i
        (linearHomComplexSingleExtToHomology.{w} k K Y i e) := by
  apply (linearHomComplexSingleHomologyEquiv k K Z i).injective
  rw [linearHomComplexSingleHomologyEquiv_postcomp]
  simp only [linearHomComplexSingleExtToHomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rw [← TauCeti.ChainComplex.extToHomology_coefficient_naturality]
  congr 1
  simp only [TauCeti.extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id,
    Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (zero_add 1)]

variable (k) in
/-- **The split decomposition of the universal coefficient sequence** of the Hom complex into
`Y[0]`: `Hⁱ(Hom(K, Y[0])) ≃ₗ[k] Ext¹(H¹⁻ⁱ(K), Y) × (H⁻ⁱ(K) ⟶ Y)`, built from
`CochainComplex.linearHomComplexSingleExtToHomology`,
`CochainComplex.linearHomComplexSingleKronecker`, and
`CochainComplex.linearHomComplexSingleKroneckerSection`. It depends on the chosen retraction of
`K.iCycles (-i)` and commutes with coefficient morphisms `Y ⟶ Z`. -/
def linearHomComplexSingleUniversalCoefficientEquiv (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k]
      Ext.{w} (K.homology (1 - i)) Y 1 × (K.homology (-i) ⟶ Y) :=
  ((exact_linearHomComplexSingleExtToHomology_linearHomComplexSingleKronecker.{w}
      (k := k) K Y i).splitSurjectiveEquiv
    (linearHomComplexSingleExtToHomology_injective K Y i)
    ⟨linearHomComplexSingleKroneckerSection k K Y i,
      LinearMap.ext (linearHomComplexSingleKronecker_linearHomComplexSingleKroneckerSection
        K Y i)⟩).val

@[simp]
lemma linearHomComplexSingleUniversalCoefficientEquiv_symm_inl (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] (e : Ext.{w} (K.homology (1 - i)) Y 1) :
    (linearHomComplexSingleUniversalCoefficientEquiv.{w} k K Y i).symm (e, 0) =
      linearHomComplexSingleExtToHomology.{w} k K Y i e :=
  (LinearMap.congr_fun
    ((exact_linearHomComplexSingleExtToHomology_linearHomComplexSingleKronecker.{w}
        (k := k) K Y i).splitSurjectiveEquiv
      (linearHomComplexSingleExtToHomology_injective K Y i) _).property.left e).symm

@[simp]
lemma linearHomComplexSingleUniversalCoefficientEquiv_symm_inr (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] (g : K.homology (-i) ⟶ Y) :
    (linearHomComplexSingleUniversalCoefficientEquiv.{w} k K Y i).symm (0, g) =
      linearHomComplexSingleKroneckerSection k K Y i g :=
  LinearMap.congr_fun (congrArg Subtype.val
    (((exact_linearHomComplexSingleExtToHomology_linearHomComplexSingleKronecker.{w}
        (k := k) K Y i).splitSurjectiveEquiv
      (linearHomComplexSingleExtToHomology_injective K Y i)).left_inv
      ⟨linearHomComplexSingleKroneckerSection k K Y i,
        LinearMap.ext (linearHomComplexSingleKronecker_linearHomComplexSingleKroneckerSection
          K Y i)⟩)) g

lemma linearHomComplexSingleUniversalCoefficientEquiv_symm_apply (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))]
    (x : Ext.{w} (K.homology (1 - i)) Y 1 × (K.homology (-i) ⟶ Y)) :
    (linearHomComplexSingleUniversalCoefficientEquiv.{w} k K Y i).symm x =
      linearHomComplexSingleExtToHomology.{w} k K Y i x.1 +
        linearHomComplexSingleKroneckerSection k K Y i x.2 := by
  have hx : x = (x.1, 0) + (0, x.2) := by ext <;> simp
  conv_lhs => rw [hx]
  rw [map_add, linearHomComplexSingleUniversalCoefficientEquiv_symm_inl,
    linearHomComplexSingleUniversalCoefficientEquiv_symm_inr]

@[simp]
lemma linearHomComplexSingleUniversalCoefficientEquiv_linearHomComplexSingleExtToHomology (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] (e : Ext.{w} (K.homology (1 - i)) Y 1) :
    linearHomComplexSingleUniversalCoefficientEquiv.{w} k K Y i
        (linearHomComplexSingleExtToHomology.{w} k K Y i e) = (e, 0) := by
  rw [← linearHomComplexSingleUniversalCoefficientEquiv_symm_inl K Y i e,
    LinearEquiv.apply_symm_apply]

@[simp]
lemma linearHomComplexSingleUniversalCoefficientEquiv_linearHomComplexSingleKroneckerSection
    (i : ℤ) [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] (g : K.homology (-i) ⟶ Y) :
    linearHomComplexSingleUniversalCoefficientEquiv.{w} k K Y i
        (linearHomComplexSingleKroneckerSection k K Y i g) = (0, g) := by
  rw [← linearHomComplexSingleUniversalCoefficientEquiv_symm_inr K Y i g,
    LinearEquiv.apply_symm_apply]

@[simp]
lemma linearHomComplexSingleUniversalCoefficientEquiv_apply_snd (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))]
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    (linearHomComplexSingleUniversalCoefficientEquiv.{w} k K Y i x).2 =
      linearHomComplexSingleKronecker k K Y i x :=
  (LinearMap.congr_fun
    ((exact_linearHomComplexSingleExtToHomology_linearHomComplexSingleKronecker.{w}
        (k := k) K Y i).splitSurjectiveEquiv
      (linearHomComplexSingleExtToHomology_injective K Y i) _).property.right x).symm

variable {Y} in
/-- For a fixed retraction of `K.iCycles (-i)`, the splitting
`CochainComplex.linearHomComplexSingleUniversalCoefficientEquiv` commutes with postcomposition by
any coefficient morphism `g : Y ⟶ Z`. -/
lemma linearHomComplexSingleUniversalCoefficientEquiv_coefficient_naturality {Z : C} (g : Y ⟶ Z)
    (i : ℤ) [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))]
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    linearHomComplexSingleUniversalCoefficientEquiv.{w} k K Z i
        (homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i x) =
      ((linearHomComplexSingleUniversalCoefficientEquiv.{w} k K Y i x).1.comp (Ext.mk₀ g)
          (add_zero 1),
        (linearHomComplexSingleUniversalCoefficientEquiv.{w} k K Y i x).2 ≫ g) := by
  apply (linearHomComplexSingleUniversalCoefficientEquiv.{w} k K Z i).symm.injective
  rw [LinearEquiv.symm_apply_apply, linearHomComplexSingleUniversalCoefficientEquiv_symm_apply,
    linearHomComplexSingleExtToHomology_coefficient_naturality,
    ← linearHomComplexSingleKroneckerSection_coefficient_naturality,
    ← map_add, ← linearHomComplexSingleUniversalCoefficientEquiv_symm_apply K Y i,
    LinearEquiv.symm_apply_apply]

end Ext

end CochainComplex
