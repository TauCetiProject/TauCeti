/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import TauCeti.Algebra.Homology.UniversalCoefficient.Basic

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
* `CochainComplex.linearHomComplexSingleKronecker`: the Kronecker map
  `Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)`, characterized by
  `CochainComplex.homologyπ_linearHomComplexSingleKronecker`.
* `CochainComplex.linearHomComplexSingleKronecker_bijective` and
  `CochainComplex.linearHomComplexSingleKroneckerEquiv`: the Kronecker map is bijective for an
  injective object `Y`.
* `CochainComplex.linearHomComplexSingleKronecker_surjective`: it is surjective when the cocycles
  of `K` split off in degree `-i`.
* `CochainComplex.linearHomComplexSingleExtToHomology`,
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

variable {C : Type*} [Category* C] [Abelian C]

section Ring

variable {k : Type*} [Ring k] [Linear k C] (K : CochainComplex C ℤ) (Y : C)

/-- The sign `(-1)^(i(i+1)/2)` relating the two differentials. -/
private def homSingleSign (i : ℤ) : ℤˣ := (i * (i + 1) / 2).negOnePow

private lemma homSingleSign_succ (i : ℤ) :
    homSingleSign (i + 1) = (i + 1).negOnePow * homSingleSign i := by
  rw [homSingleSign, homSingleSign, ← Int.negOnePow_add]
  congr 1
  have : (i + 1) * (i + 1 + 1) = i * (i + 1) + 2 * (i + 1) := by ring
  rw [this]
  omega

/-- The index of `K⁻ᵢ = K⁻ⁱ` and the degree `i` add up to zero. -/
private lemma embeddingDownIntUpInt_f_add_self (i : ℤ) :
    ComplexShape.embeddingDownIntUpInt.f i + i = 0 := by
  simp

variable (k) in
/-- In degree `i`, a cochain of degree `i` from `K` to `Y` placed in degree `0` is a morphism
`K⁻ⁱ ⟶ Y`, here twisted by the sign `(-1)^(i(i+1)/2)`. -/
private def homSingleXEquiv (i : ℤ) :
    Cochain K ((singleFunctor C 0).obj Y) i ≃ₗ[k]
      ((K.restriction ComplexShape.embeddingDownIntUpInt).X i ⟶ Y) where
  toFun α := homSingleSign i • Cochain.toSingleEquiv (embeddingDownIntUpInt_f_add_self i) α
  invFun f := homSingleSign i • Cochain.toSingleMk f (embeddingDownIntUpInt_f_add_self i)
  map_add' α β := by simp [smul_add]
  map_smul' r α := by simp [smul_comm (homSingleSign i) r]
  left_inv α := by
    simp [Units.smul_def, Cochain.toSingleMk_smul, smul_smul, ← Units.val_mul]
  right_inv f := by simp [Units.smul_def, smul_smul, ← Units.val_mul]

variable (k) in
/-- `CochainComplex.homSingleXEquiv` as an isomorphism between the terms of degree `i` of the two
complexes. -/
private def homSingleXIso (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).X i ≅
      (ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).X i :=
  (homSingleXEquiv k K Y i).toModuleIso

private lemma homSingleXIso_hom_apply (i : ℤ) (α : Cochain K ((singleFunctor C 0).obj Y) i) :
    (homSingleXIso k K Y i).hom α =
      homSingleSign i • Cochain.toSingleEquiv (embeddingDownIntUpInt_f_add_self i) α :=
  rfl

/-- The isomorphisms `CochainComplex.homSingleXIso` commute with the differentials. -/
private lemma homSingle_comm (i : ℤ) (α : Cochain K ((singleFunctor C 0).obj Y) i) :
    (K.restriction ComplexShape.embeddingDownIntUpInt).d (i + 1) i ≫
        (homSingleSign i • Cochain.toSingleEquiv (embeddingDownIntUpInt_f_add_self i) α) =
      homSingleSign (i + 1) •
        Cochain.toSingleEquiv (embeddingDownIntUpInt_f_add_self (i + 1)) (δ i (i + 1) α) := by
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective α _ (embeddingDownIntUpInt_f_add_self i)
  rw [Cochain.δ_toSingleMk f (embeddingDownIntUpInt_f_add_self i) (i + 1)
    (ComplexShape.embeddingDownIntUpInt.f (i + 1)) (embeddingDownIntUpInt_f_add_self _)]
  simp [homSingleSign_succ, smul_smul, mul_right_comm _ (homSingleSign i)]

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
  (rfl)

/-- In degree `i`, the inverse of `CochainComplex.linearHomComplexSingleIso` sends a morphism
`f : K⁻ⁱ ⟶ Y` to the cochain of degree `i` it defines (`HomComplex.Cochain.toSingleMk`),
multiplied by the sign `(-1)^(i(i+1)/2)`. -/
lemma linearHomComplexSingleIso_inv_f_apply (i : ℤ)
    (f : (K.restriction ComplexShape.embeddingDownIntUpInt).X i ⟶ Y) :
    (linearHomComplexSingleIso k K Y).inv.f i f =
      (i * (i + 1) / 2).negOnePow • Cochain.toSingleMk (p := -i) f (neg_add_cancel i) :=
  (rfl)

/-! ### The Kronecker map -/

/-- The cycles of `K⁻` in degree `i` are those of `K` in degree `j = -i`. -/
private def negCyclesIso (i j : ℤ) (h : i + j = 0) :
    (K.restriction ComplexShape.embeddingDownIntUpInt).cycles i ≅ K.cycles j :=
  K.restrictionCyclesIso ComplexShape.embeddingDownIntUpInt i (i - 1)
    ((ComplexShape.down ℤ).next_eq' (by simp)) (j' := j) (k' := j + 1) (by simp; omega)
    (by simp; omega) ((ComplexShape.up ℤ).next_eq' (by simp))

@[reassoc]
private lemma negCyclesIso_hom_iCycles (i j : ℤ) (h : i + j = 0) :
    (negCyclesIso K i j h).hom ≫ K.iCycles j =
      (K.restriction ComplexShape.embeddingDownIntUpInt).iCycles i ≫
        (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
          (show ComplexShape.embeddingDownIntUpInt.f i = j by simp; omega)).hom :=
  K.restrictionCyclesIso_hom_iCycles ..

@[reassoc]
private lemma negCyclesIso_inv_iCycles (i j : ℤ) (h : i + j = 0) :
    (negCyclesIso K i j h).inv ≫ (K.restriction ComplexShape.embeddingDownIntUpInt).iCycles i =
      K.iCycles j ≫ (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
          (show ComplexShape.embeddingDownIntUpInt.f i = j by simp; omega)).inv :=
  K.restrictionCyclesIso_inv_iCycles ..

/-- The homology of `K⁻` in degree `i` is that of `K` in degree `j = -i`. -/
private def negHomologyIso (i j : ℤ) (h : i + j = 0) :
    (K.restriction ComplexShape.embeddingDownIntUpInt).homology i ≅ K.homology j :=
  K.restrictionHomologyIso ComplexShape.embeddingDownIntUpInt (i + 1) i (i - 1)
    ((ComplexShape.down ℤ).prev_eq' (by simp)) ((ComplexShape.down ℤ).next_eq' (by simp))
    (i' := j - 1) (k' := j + 1) (by simp; omega) (by simp; omega) (by simp; omega)
    ((ComplexShape.up ℤ).prev_eq' (by simp)) ((ComplexShape.up ℤ).next_eq' (by simp))

@[reassoc]
private lemma homologyπ_negHomologyIso_inv (i j : ℤ) (h : i + j = 0) :
    K.homologyπ j ≫ (negHomologyIso K i j h).inv =
      (negCyclesIso K i j h).inv ≫ (K.restriction ComplexShape.embeddingDownIntUpInt).homologyπ i :=
  K.homologyπ_restrictionHomologyIso_inv ..

/-- If the cycles of `K` split off in degree `j = -i`, then those of `K⁻` split off in degree
`i`. -/
private lemma isSplitMono_restriction_iCycles (i j : ℤ) (h : i + j = 0)
    [IsSplitMono (K.iCycles j)] :
    IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles i) :=
  IsSplitMono.mk'
    { retraction := (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
        (show ComplexShape.embeddingDownIntUpInt.f i = j by simp; omega)).hom ≫
          retraction (K.iCycles j) ≫ (negCyclesIso K i j h).inv
      id := by rw [← negCyclesIso_hom_iCycles_assoc K i j h, IsSplitMono.id_assoc, Iso.hom_inv_id] }

/-- If the cycles of `K` are projective in degree `j = -i`, then so are those of `K⁻` in degree
`i`. -/
private lemma projective_restriction_cycles (i j : ℤ) (h : i + j = 0)
    [Projective (K.cycles j)] :
    Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).cycles i) :=
  Projective.of_iso (negCyclesIso K i j h).symm inferInstance

variable (k) in
/-- The `k`-linear equivalence between the cohomology of the Hom complex `Hom(K, Y[0])` and that of
the linear Yoneda complex `Hom(K⁻, Y)` in degree `i`, induced by
`CochainComplex.linearHomComplexSingleIso` and corrected by the sign `(-1)^(i(i+1)/2)`, so that
it is induced by the identification `HomComplex.Cochain.toSingleEquiv` of the terms. -/
private def homSingleHomologyEquiv (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k]
      (ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k
        Y).homology i where
  toFun x := homSingleSign i • homologyMap (linearHomComplexSingleIso k K Y).hom i x
  invFun x := homSingleSign i • homologyMap (linearHomComplexSingleIso k K Y).inv i x
  map_add' x y := by simp [smul_add]
  map_smul' r x := by simp [smul_comm (homSingleSign i) r]
  left_inv x := by
    dsimp only
    rw [Units.smul_def, Units.smul_def, map_zsmul, smul_smul, ← ModuleCat.comp_apply,
      ← homologyMap_comp, Iso.hom_inv_id, homologyMap_id, ModuleCat.id_apply, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, one_smul]
  right_inv x := by
    dsimp only
    rw [Units.smul_def, Units.smul_def, map_zsmul, smul_smul, ← ModuleCat.comp_apply,
      ← homologyMap_comp, Iso.inv_hom_id, homologyMap_id, ModuleCat.id_apply, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, one_smul]

/-- Transporting a morphism `K.X p ⟶ Y` given by a cochain to `Y[q]` along an equality of indices
`p' = p` gives the morphism `K.X p' ⟶ Y` of the same cochain. -/
private lemma eqToHom_toSingleEquiv {p p' n q : ℤ} (hp : p' = p) (h : p + n = q)
    (h' : p' + n = q) (e : K.X p' = K.X p) (α : Cochain K ((singleFunctor C q).obj Y) n) :
    eqToHom e ≫ Cochain.toSingleEquiv h α = Cochain.toSingleEquiv h' α := by
  subst hp
  simp

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
  (Linear.homCongr k (negHomologyIso K i (-i) (add_neg_cancel i)) (Iso.refl Y)).toLinearMap ∘ₗ
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
  set ψ := cyclesMap (linearHomComplexSingleIso k K Y).hom i φ
  have h₁ : homologyMap (linearHomComplexSingleIso k K Y).hom i
      ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ) =
        (ChainComplex.linearYonedaObj _ k Y).homologyπ i ψ := by
    rw [← ConcreteCategory.comp_apply, homologyπ_naturality, ConcreteCategory.comp_apply]
  have h₂ : (ChainComplex.linearYonedaObj _ k Y).iCycles i ψ =
      homSingleSign i • Cochain.toSingleEquiv (embeddingDownIntUpInt_f_add_self i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) := by
    rw [← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply]
    exact homSingleXIso_hom_apply K Y i _
  simp only [linearHomComplexSingleKronecker, homSingleHomologyEquiv, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Linear.homCongr_apply, h₁, Units.smul_def, map_zsmul, Iso.refl_hom, Category.comp_id,
    Preadditive.comp_zsmul, homologyπ_negHomologyIso_inv_assoc,
    TauCeti.ChainComplex.kronecker_homologyπ, h₂, negCyclesIso_inv_iCycles_assoc]
  rw [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul, restrictionXIso,
    eqToIso.inv, eqToHom_toSingleEquiv K Y (by simp)]

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
  have := isSplitMono_restriction_iCycles K i (-i) (add_neg_cancel i)
  rw [linearHomComplexSingleKronecker, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (LinearEquiv.surjective _).comp
    ((TauCeti.ChainComplex.kronecker_surjective_of_isSplitMono i).comp (LinearEquiv.surjective _))

end Ring

/-! ### The `Ext` term of the universal coefficient sequence -/

section Ext

universe w

variable {k : Type*} [CommRing k] [Linear k C] [HasExt.{w} C] (K : CochainComplex C ℤ) (Y : C)

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
  haveI := projective_restriction_cycles K (i - 1) (1 - i) (by omega)
  haveI := isSplitMono_restriction_iCycles K (i - 1) (1 - i) (by omega)
  (homSingleHomologyEquiv k K Y i).symm.toLinearMap ∘ₗ
    TauCeti.ChainComplex.extToHomology k _ Y i (i - 1) ∘ₗ
      (TauCeti.extLinearEquivOfIso k (negHomologyIso K (i - 1) (1 - i) (by omega)).symm
        (Iso.refl Y) 1).toLinearMap

/-- **Injectivity in the universal coefficient sequence** of the Hom complex into `Y[0]`: the map
`Ext¹(H¹⁻ⁱ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))` is injective. -/
theorem linearHomComplexSingleExtToHomology_injective (i : ℤ) [Projective (K.cycles (1 - i))]
    [IsSplitMono (K.iCycles (1 - i))] :
    Function.Injective (linearHomComplexSingleExtToHomology.{w} k K Y i) := by
  have := projective_restriction_cycles K (i - 1) (1 - i) (by omega)
  have := isSplitMono_restriction_iCycles K (i - 1) (1 - i) (by omega)
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
  have := projective_restriction_cycles K (i - 1) (1 - i) (by omega)
  have := isSplitMono_restriction_iCycles K (i - 1) (1 - i) (by omega)
  rw [linearHomComplexSingleExtToHomology, linearHomComplexSingleKronecker,
    LinearEquiv.postcomp_exact_iff_exact, LinearEquiv.conj_symm_exact_iff_exact,
    LinearEquiv.precomp_exact_iff_exact]
  exact TauCeti.ChainComplex.exact_extToHomology_kronecker (sub_add_cancel i 1)

end Ext

end CochainComplex
