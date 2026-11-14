/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.BaseChange
public import TauCeti.FieldTheory.FunctionField.Belyi.CoefficientDescent
public import TauCeti.FieldTheory.FunctionField.Belyi.Model
import TauCeti.FieldTheory.FunctionField.ConstantExtension.RatFunc
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Regular
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import TauCeti.FieldTheory.FunctionField.SeparablyGenerated
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Descent of algebraic Belyi pairs to extensions of their field of moduli

Let `X = (F, k(t) ↪ F)` be an algebraic Belyi pair over a field `k` of characteristic zero — for
instance `ℂ` or `AlgebraicClosure ℚ`. At any degree-one place `P` of `X` lying over a rational
point `t = q` (`q ∈ ℚ \ {0, 1}`), `TauCeti.AlgebraicBelyiPair.exists_generator_finrank_adjoin_eq`
produces a normalized primitive element `z` of `F / k(t)` whose minimal polynomial has coefficients
in `K(t)`, where `K = X.pointedFieldOfModuli P` is the fixed field of the pointed stabilizer of
`P`.

Because `F = K(t)(z) · k` and `[K(t)(z) : K(t)] = [F : k(t)]`, our transcendental base-change
descent theorem `TauCeti.isAlgebraicBelyiPair_of_finrank_eq` applies directly — with no
algebraicity assumption on `k / K` — to show that `K` is the exact constant field of `K(t)(z)` and
that `K(t)(z) / K(t)` is an algebraic Belyi pair over `K`, giving an explicit `Model K X`
(`TauCeti.AlgebraicBelyiPair.pointedModel`).

Over an algebraically closed field `k` of characteristic zero (such as `ℂ`), every place of `X` has
degree `1` and the fibre over `t = 2` is nonempty. Taking `P` in that fibre proves **Köck's Theorem
(2.2)**: every isomorphism class `c` of algebraic Belyi pairs over `k` is defined over a finite
extension `K` of its field of moduli `c.fieldOfModuli` of relative degree at most `c.degree`
(`TauCeti.AlgebraicBelyiPair.IsoClass.exists_relfinrank_le_degree_isDefinedOver`). Moreover, when
the covering `X / k(t)` is normal (Galois),
`X.pointedFieldOfModuli P = (IsoClass.mk X).fieldOfModuli`, so `X` descends directly to its field
of moduli (`TauCeti.AlgebraicBelyiPair.modelOfNormal`).

We also record `TauCeti.AlgebraicBelyiPair.Model.ofBaseChange`, showing that every pair `Y` over `K`
is canonically a model of `Y.baseChange k`.

## Main definitions

* `TauCeti.AlgebraicBelyiPair.pointedModel`: the model of `X` over `X.pointedFieldOfModuli P`
  determined by a degree-one place `P` over `t = q` (`q ∈ ℚ \ {0, 1}`).
* `TauCeti.AlgebraicBelyiPair.modelOfNormal`: over an algebraically closed field `k`, a model of a
  normal Belyi covering `X / k(t)` over its field of moduli `(IsoClass.mk X).fieldOfModuli`.
* `TauCeti.AlgebraicBelyiPair.Model.ofBaseChange`: `Y` as a model of `Y.baseChange k`.

## Main results

* `TauCeti.AlgebraicBelyiPair.pointedFieldOfModuli_eq_fieldOfModuli_of_normal`: for a Galois Belyi
  covering, the pointed fixed field over any rational point `t = q` equals the field of moduli.
* `TauCeti.AlgebraicBelyiPair.exists_relfinrank_le_finrank_model` and
  `TauCeti.AlgebraicBelyiPair.IsoClass.exists_relfinrank_le_degree_isDefinedOver`: **Köck's Theorem
  (2.2)** — every Belyi pair over an algebraically closed field `k` of characteristic zero is
  defined over a finite extension of its field of moduli of degree at most `[X : k(t)]`.
* `TauCeti.AlgebraicBelyiPair.IsoClass.isDefinedOver_fieldOfModuli_of_normal`: every Galois Belyi
  covering over an algebraically closed field of characteristic zero is defined over its field of
  moduli.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  (2.2) Theorem.
-/

public section

open Polynomial IntermediateField
open scoped TensorProduct

namespace TauCeti.AlgebraicBelyiPair

universe u

/-- Rewrites the `Model.adjoin_range_embedding` condition as `constantCompositum = ⊤`. -/
private theorem adjoin_range_eq_top_iff_constantCompositum_eq_top
    {F₀ k' F' : Type*} [Field F₀] [Field k'] [Field F'] [Algebra F₀ F'] [Algebra k' F'] :
    IntermediateField.adjoin k' (Set.range (algebraMap F₀ F')) = ⊤ ↔
      constantCompositum F₀ k' F' = ⊤ := by
  simp only [← IntermediateField.toSubfield_inj, IntermediateField.top_toSubfield,
    constantCompositum_def, IntermediateField.adjoin_toSubfield, Set.union_comm]

section BaseChangeModel

variable {K k : Type u} [Field K] [CharZero K] [Field k] [CharZero k] [Algebra K k]

/-- Every algebraic Belyi pair `Y` over `K` is canonically a model over `K` of its base change
`Y.baseChange k`, whether `k / K` is algebraic or transcendental. -/
noncomputable def Model.ofBaseChange (Y : AlgebraicBelyiPair K) : Model K (Y.baseChange k) where
  pair := Y
  embedding := (Y.toBaseChange k).toRingHom
  embedding_algebraMap c := (Y.toBaseChange k).commutes c
  embedding_algebraMap_X := Y.toBaseChange_algebraMap_X k
  adjoin_range_embedding :=
    adjoin_range_eq_top_iff_constantCompositum_eq_top.mpr (Y.constantCompositum_baseChange_eq_top k)

/-- The base change of any isomorphism class over `K` to `k` is defined over `K`. -/
theorem IsoClass.isDefinedOver_baseChange (c : IsoClass K) :
    (c.baseChange k).IsDefinedOver K := by
  induction c using IsoClass.ind with
  | h Y =>
    rw [IsoClass.baseChange_mk, IsoClass.isDefinedOver_mk_iff]
    exact ⟨Model.ofBaseChange Y⟩

end BaseChangeModel

section PointedDescent

variable {k : Type u} [Field k] [CharZero k] (X : AlgebraicBelyiPair k)

/-- **For a Galois Belyi covering, the pointed fixed field over any rational point equals the field
of moduli.** -/
theorem pointedFieldOfModuli_eq_fieldOfModuli_of_normal [Normal (RatFunc k) X]
    {P : Place k X} {q : ℚ}
    (hP : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k))) :
    X.pointedFieldOfModuli P = (IsoClass.mk X).fieldOfModuli := by
  rw [pointedFieldOfModuli_def, IsoClass.fieldOfModuli_def,
    X.pointedStabilizer_eq_stabilizer_of_normal hP]

variable {X}

/-- Existence of a sub-Belyi-pair inside `X` over `K = X.pointedFieldOfModuli P` attached to a
degree-one place `P` over `t = q` (`q ∈ ℚ \ {0, 1}`). -/
private theorem exists_pointed_subpair {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) :
    ∃ (Y : AlgebraicBelyiPair (X.pointedFieldOfModuli P)) (φ : Y →+* X),
      (∀ c : X.pointedFieldOfModuli P,
        φ (algebraMap (X.pointedFieldOfModuli P) Y c) =
          algebraMap k X (algebraMap (X.pointedFieldOfModuli P) k c)) ∧
      φ (algebraMap (RatFunc (X.pointedFieldOfModuli P)) Y RatFunc.X) =
        algebraMap (RatFunc k) X RatFunc.X ∧
      IntermediateField.adjoin k (Set.range φ) = ⊤ := by
  let K := X.pointedFieldOfModuli P
  have hXK : Transcendental K (RatFunc.X : RatFunc k) :=
    fun ha ↦ RatFunc.transcendental_X (ha.tower_top k)
  let _ : Algebra (RatFunc K) (RatFunc k) := ratFuncAlgebraOfTranscendental hXK
  have : IsScalarTower K (RatFunc K) (RatFunc k) :=
    isScalarTower_ratFuncAlgebraOfTranscendental hXK
  let _ : Algebra (RatFunc K) X :=
    ((algebraMap (RatFunc k) X).comp (algebraMap (RatFunc K) (RatFunc k))).toAlgebra
  have : IsScalarTower (RatFunc K) (RatFunc k) X := .of_algebraMap_eq' rfl
  have : IsScalarTower K (RatFunc K) X := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply K k X, IsScalarTower.algebraMap_apply k (RatFunc k) X,
      ← IsScalarTower.algebraMap_apply K k (RatFunc k),
      IsScalarTower.algebraMap_apply K (RatFunc K) (RatFunc k),
      ← IsScalarTower.algebraMap_apply (RatFunc K) (RatFunc k) X]
  have hX : algebraMap (RatFunc K) (RatFunc k) RatFunc.X = RatFunc.X :=
    algebraMap_ratFuncAlgebraOfTranscendental_X hXK
  have hC : ∀ c : K,
      algebraMap (RatFunc K) (RatFunc k) (RatFunc.C c) = RatFunc.C (c : k) := fun c ↦ by
    rw [← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply K (RatFunc K) (RatFunc k),
      IsScalarTower.algebraMap_apply K k (RatFunc k), RatFunc.algebraMap_eq_C]
    rfl
  obtain ⟨z, hgen, hz, -, hfin⟩ := exists_generator_finrank_adjoin_eq hq₀ hq₁ hPa hP hC hX
  let F₀ : IntermediateField (RatFunc K) X := (RatFunc K)⟮z⟯
  have : FiniteDimensional (RatFunc K) F₀ := IntermediateField.adjoin.finiteDimensional hz
  have hcomp : constantCompositum F₀ k X = ⊤ :=
    constantCompositum_adjoin_simple_ratFunc_eq_top hX hgen
  have hXF₀ : algebraMap F₀ X (algebraMap (RatFunc K) F₀ RatFunc.X) =
      algebraMap (RatFunc k) X RatFunc.X := by
    rw [← IsScalarTower.algebraMap_apply (RatFunc K) F₀ X,
      IsScalarTower.algebraMap_apply (RatFunc K) (RatFunc k) X, hX]
  exact ⟨⟨F₀, isAlgebraicBelyiPair_of_finrank_eq X.isAlgebraicBelyiPair hcomp hXF₀ hfin⟩,
    algebraMap F₀ X, fun c ↦ (IsScalarTower.algebraMap_apply K F₀ X c).symm.trans
      (IsScalarTower.algebraMap_apply K k X c),
    hXF₀, adjoin_range_eq_top_iff_constantCompositum_eq_top.mpr hcomp⟩

/-- **Explicit model over the pointed fixed field**: a degree-one place `P` of `X` over a rational
point `t = q` (`q ∈ ℚ \ {0, 1}`) produces an explicit model of `X` over
`X.pointedFieldOfModuli P`, without any algebraicity assumption on `k`. -/
noncomputable def pointedModel {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) :
    Model (X.pointedFieldOfModuli P) X :=
  let h := X.exists_pointed_subpair hq₀ hq₁ hPa hP
  { pair := h.choose
    embedding := h.choose_spec.choose
    embedding_algebraMap := h.choose_spec.choose_spec.1
    embedding_algebraMap_X := h.choose_spec.choose_spec.2.1
    adjoin_range_embedding := h.choose_spec.choose_spec.2.2 }

/-- The degree of `X.pointedModel` over `K(t)` equals the degree of `X` over `k(t)`. -/
@[simp]
theorem finrank_pointedModel_pair {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) :
    Module.finrank (RatFunc (X.pointedFieldOfModuli P)) (X.pointedModel hq₀ hq₁ hPa hP).pair =
      Module.finrank (RatFunc k) X := by
  let M := X.pointedModel hq₀ hq₁ hPa hP
  let _ : Algebra M.pair X := M.embedding.toAlgebra
  have : IsScalarTower (X.pointedFieldOfModuli P) M.pair X :=
    .of_algebraMap_eq fun c ↦ (M.embedding_algebraMap c).symm
  have hcomp : constantCompositum M.pair k X = ⊤ :=
    adjoin_range_eq_top_iff_constantCompositum_eq_top.mp M.adjoin_range_embedding
  have hF : IsFunctionField (X.pointedFieldOfModuli P) M.pair :=
    (IsFunctionField.ratFunc _).finite_extension
  obtain ⟨x₀, hx₀, _⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  have : Algebra.IsGeometricallyReduced (X.pointedFieldOfModuli P) M.pair :=
    isGeometricallyReduced_of_separating hx₀
  exact (finrank_ratFunc_eq_of_isGeometricallyReduced
    M.pair.isAlgebraicBelyiPair.isIntegrallyClosedIn hcomp M.embedding_algebraMap_X).symm

/-- Transport a model along an equality of intermediate subfields of `k`. -/
private noncomputable def Model.castIntermediateField {K₁ K₂ : IntermediateField ℚ k}
    (h : K₁ = K₂) (M : Model K₁ X) : Model K₂ X :=
  h ▸ M

section IsAlgClosed

variable [IsAlgClosed k]

/-- Over an algebraically closed field `k` of characteristic zero, there exists a degree-one place
of `X` lying over `t = 2`. -/
private theorem exists_place_over_two (X : AlgebraicBelyiPair k) :
    ∃ P : Place k X,
      P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C ((2 : ℚ) : k)) ∧
        P.degree = 1 := by
  have hF : IsFunctionField k X := (IsFunctionField.ratFunc k).finite_extension
  obtain ⟨P, hPa⟩ := Place.restrict_surjective_of_finiteDimensional
    (IsFunctionField.ratFunc k) hF (Place.adicOfIrreducible (irreducible_X_sub_C ((2 : ℚ) : k)))
  have := P.finiteDimensional_residueField hF
  exact ⟨P, hPa, P.degree_eq_one_of_isAlgClosed_of_isIntegral⟩

/-- **Köck's Theorem (2.2) for pairs**: every algebraic Belyi pair `X` over an algebraically closed
field `k` of characteristic zero (such as `ℂ` or `AlgebraicClosure ℚ`) admits a model over a finite
extension `K` of `(IsoClass.mk X).fieldOfModuli` of degree `0 < [K : M(X)] ≤ [X : k(t)]`. -/
theorem exists_relfinrank_le_finrank_model (X : AlgebraicBelyiPair k) :
    ∃ K : IntermediateField ℚ k,
      (IsoClass.mk X).fieldOfModuli ≤ K ∧
        0 < (IsoClass.mk X).fieldOfModuli.relfinrank K ∧
        (IsoClass.mk X).fieldOfModuli.relfinrank K ≤ Module.finrank (RatFunc k) X ∧
        Nonempty (Model K X) := by
  obtain ⟨P, hPa, hP⟩ := exists_place_over_two X
  have h20 : ((2 : ℚ) : k) ≠ 0 := by norm_num
  have h21 : ((2 : ℚ) : k) ≠ 1 := by norm_num
  exact ⟨X.pointedFieldOfModuli P, X.fieldOfModuli_le_pointedFieldOfModuli P,
    X.relfinrank_pointedFieldOfModuli_pos hPa, X.relfinrank_pointedFieldOfModuli_le hPa,
    ⟨X.pointedModel h20 h21 hPa hP⟩⟩

/-- **Köck's Theorem (2.2) for isomorphism classes**: every isomorphism class `c` of algebraic Belyi
pairs over an algebraically closed field `k` of characteristic zero is defined over a finite
extension `K` of its field of moduli `c.fieldOfModuli` of relative degree
`0 < [K : M(c)] ≤ deg c`. -/
theorem IsoClass.exists_relfinrank_le_degree_isDefinedOver (c : IsoClass k) :
    ∃ K : IntermediateField ℚ k,
      c.fieldOfModuli ≤ K ∧
        0 < c.fieldOfModuli.relfinrank K ∧
        c.fieldOfModuli.relfinrank K ≤ c.degree ∧
        c.IsDefinedOver K := by
  induction c using IsoClass.ind with
  | h X =>
    obtain ⟨K, hle, hpos, hdeg, hM⟩ := exists_relfinrank_le_finrank_model X
    exact ⟨K, hle, hpos, (IsoClass.degree_mk X).symm ▸ hdeg, IsoClass.isDefinedOver_mk_iff.mpr hM⟩

/-- **A Galois Belyi covering over an algebraically closed field of characteristic zero has an
explicit model over its field of moduli.** -/
noncomputable def modelOfNormal (X : AlgebraicBelyiPair k) [Normal (RatFunc k) X] :
    Model (IsoClass.mk X).fieldOfModuli X :=
  let h := exists_place_over_two X
  have h20 : ((2 : ℚ) : k) ≠ 0 := by norm_num
  have h21 : ((2 : ℚ) : k) ≠ 1 := by norm_num
  Model.castIntermediateField
    (X.pointedFieldOfModuli_eq_fieldOfModuli_of_normal h.choose_spec.1)
    (X.pointedModel h20 h21 h.choose_spec.1 h.choose_spec.2)

/-- **Every Galois Belyi covering over an algebraically closed field of characteristic zero is
defined over its field of moduli.** -/
theorem IsoClass.isDefinedOver_fieldOfModuli_of_normal (X : AlgebraicBelyiPair k)
    [Normal (RatFunc k) X] :
    (IsoClass.mk X).IsDefinedOver (IsoClass.mk X).fieldOfModuli :=
  IsoClass.isDefinedOver_mk_iff.mpr ⟨modelOfNormal X⟩

end IsAlgClosed

end PointedDescent

end TauCeti.AlgebraicBelyiPair
