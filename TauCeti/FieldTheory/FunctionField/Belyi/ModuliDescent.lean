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
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Descent of algebraic Belyi pairs to extensions of their field of moduli

For an algebraic Belyi pair `X` over a field `k` of characteristic zero and any degree-one place `P`
of `X` over `t = q` (`q ∈ ℚ \ {0, 1}`), `exists_generator_finrank_adjoin_eq` and
`isAlgebraicBelyiPair_of_finrank_eq` construct an explicit `Model K X` over
`K = X.pointedFieldOfModuli P` (`TauCeti.AlgebraicBelyiPair.pointedModel`) without algebraicity
assumptions on `k / K`. Over an algebraically closed field `k` of characteristic zero, choosing `P`
over `t = 2` proves **Köck's Theorem (2.2)**: every isomorphism class `c` is defined over an
extension `K` of `c.fieldOfModuli` with `0 < [K : M(c)] ≤ deg c`, and every Galois Belyi covering
is defined over its field of moduli.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  (2.2) Theorem.
-/

public section

open Polynomial IntermediateField
open scoped TensorProduct

namespace TauCeti.AlgebraicBelyiPair

universe u

private theorem adjoin_range_eq_top_iff_constantCompositum_eq_top
    {F₀ k' F' : Type*} [Field F₀] [Field k'] [Field F'] [Algebra F₀ F'] [Algebra k' F'] :
    IntermediateField.adjoin k' (Set.range (algebraMap F₀ F')) = ⊤ ↔
      constantCompositum F₀ k' F' = ⊤ := by
  simp only [← IntermediateField.toSubfield_inj, IntermediateField.top_toSubfield,
    constantCompositum_def, IntermediateField.adjoin_toSubfield, Set.union_comm]

section BaseChangeModel

variable {K k : Type u} [Field K] [CharZero K] [Field k] [CharZero k] [Algebra K k]

/-- Every algebraic Belyi pair `Y` over `K` is canonically a model over `K` of `Y.baseChange k`. -/
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
  | h Y => rw [IsoClass.baseChange_mk, IsoClass.isDefinedOver_mk_iff]; exact ⟨.ofBaseChange Y⟩

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

private theorem exists_pointed_subpair {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) :
    ∃ (Y : AlgebraicBelyiPair (X.pointedFieldOfModuli P)) (φ : Y →+* X),
      (∀ c : X.pointedFieldOfModuli P, φ (algebraMap _ Y c) = algebraMap k X (algebraMap _ k c)) ∧
      φ (algebraMap (RatFunc (X.pointedFieldOfModuli P)) Y RatFunc.X) =
        algebraMap (RatFunc k) X RatFunc.X ∧
      IntermediateField.adjoin k (Set.range φ) = ⊤ ∧
      Module.finrank (RatFunc (X.pointedFieldOfModuli P)) Y = Module.finrank (RatFunc k) X := by
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
  have hC (c : K) : algebraMap (RatFunc K) (RatFunc k) (RatFunc.C c) = RatFunc.C (c : k) := by
    rw [← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply K (RatFunc K) (RatFunc k),
      IsScalarTower.algebraMap_apply K k (RatFunc k), RatFunc.algebraMap_eq_C]; rfl
  obtain ⟨z, hgen, hz, -, hfin⟩ := exists_generator_finrank_adjoin_eq hq₀ hq₁ hPa hP hC hX
  let F₀ : IntermediateField (RatFunc K) X := (RatFunc K)⟮z⟯
  have : FiniteDimensional (RatFunc K) F₀ := IntermediateField.adjoin.finiteDimensional hz
  have hcomp : constantCompositum F₀ k X = ⊤ := constantCompositum_adjoin_simple_ratFunc_eq_top
    hX hgen
  have hXF₀ : algebraMap F₀ X (algebraMap (RatFunc K) F₀ RatFunc.X) =
      algebraMap (RatFunc k) X RatFunc.X := by
    rw [← IsScalarTower.algebraMap_apply (RatFunc K) F₀ X,
      IsScalarTower.algebraMap_apply (RatFunc K) (RatFunc k) X, hX]
  exact ⟨⟨F₀, isAlgebraicBelyiPair_of_finrank_eq X.isAlgebraicBelyiPair hcomp hXF₀ hfin⟩,
    algebraMap F₀ X, fun c ↦ (IsScalarTower.algebraMap_apply K F₀ X c).symm.trans
      (IsScalarTower.algebraMap_apply K k X c),
    hXF₀, adjoin_range_eq_top_iff_constantCompositum_eq_top.mpr hcomp, hfin⟩

/-- **Explicit model over the pointed fixed field** for a rational place `P` over `t = q`. -/
noncomputable def pointedModel {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) : Model (X.pointedFieldOfModuli P) X :=
  let h := X.exists_pointed_subpair hq₀ hq₁ hPa hP
  { pair := h.choose
    embedding := h.choose_spec.choose
    embedding_algebraMap := h.choose_spec.choose_spec.1
    embedding_algebraMap_X := h.choose_spec.choose_spec.2.1
    adjoin_range_embedding := h.choose_spec.choose_spec.2.2.1 }

@[simp] theorem finrank_pointedModel_pair {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) :
    Module.finrank (RatFunc (X.pointedFieldOfModuli P)) (X.pointedModel hq₀ hq₁ hPa hP).pair =
      Module.finrank (RatFunc k) X :=
  (X.exists_pointed_subpair hq₀ hq₁ hPa hP).choose_spec.choose_spec.2.2.2

section IsAlgClosed

variable [IsAlgClosed k]

private theorem exists_place_over_two (X : AlgebraicBelyiPair k) :
    ∃ P : Place k X,
      P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C ((2 : ℚ) : k)) ∧
        P.degree = 1 := by
  have hF : IsFunctionField k X := (IsFunctionField.ratFunc k).finite_extension
  obtain ⟨P, hPa⟩ := Place.restrict_surjective_of_finiteDimensional
    (IsFunctionField.ratFunc k) hF (Place.adicOfIrreducible (irreducible_X_sub_C ((2 : ℚ) : k)))
  have := P.finiteDimensional_residueField hF
  exact ⟨P, hPa, P.degree_eq_one_of_isAlgClosed_of_isIntegral⟩

/-- **Köck's Theorem (2.2) for pairs**: every Belyi pair `X` over algebraically closed `k` has a
model over an extension `K` of `M(X)` with `0 < [K : M(X)] ≤ [X : k(t)]`. -/
theorem exists_relfinrank_le_finrank_model (X : AlgebraicBelyiPair k) :
    ∃ K : IntermediateField ℚ k, (IsoClass.mk X).fieldOfModuli ≤ K ∧
      0 < (IsoClass.mk X).fieldOfModuli.relfinrank K ∧
      (IsoClass.mk X).fieldOfModuli.relfinrank K ≤ Module.finrank (RatFunc k) X ∧
      Nonempty (Model K X) := by
  obtain ⟨P, hPa, hP⟩ := exists_place_over_two X
  exact ⟨X.pointedFieldOfModuli P, X.fieldOfModuli_le_pointedFieldOfModuli P,
    X.relfinrank_pointedFieldOfModuli_pos hPa, X.relfinrank_pointedFieldOfModuli_le hPa,
    ⟨X.pointedModel (by norm_num) (by norm_num) hPa hP⟩⟩

/-- **Köck's Theorem (2.2) for isomorphism classes**: every `c` over algebraically closed `k` is
defined over an extension `K` of `c.fieldOfModuli` with `0 < [K : M(c)] ≤ deg c`. -/
theorem IsoClass.exists_relfinrank_le_degree_isDefinedOver (c : IsoClass k) :
    ∃ K : IntermediateField ℚ k, c.fieldOfModuli ≤ K ∧ 0 < c.fieldOfModuli.relfinrank K ∧
      c.fieldOfModuli.relfinrank K ≤ c.degree ∧ c.IsDefinedOver K := by
  induction c using IsoClass.ind with
  | h X =>
    obtain ⟨K, hle, hpos, hdeg, hM⟩ := exists_relfinrank_le_finrank_model X
    exact ⟨K, hle, hpos, (IsoClass.degree_mk X).symm ▸ hdeg, IsoClass.isDefinedOver_mk_iff.mpr hM⟩

/-- Explicit model over the field of moduli for a Galois Belyi covering over algebraically closed
`k`. -/
noncomputable def modelOfNormal (X : AlgebraicBelyiPair k) [Normal (RatFunc k) X] :
    Model (IsoClass.mk X).fieldOfModuli X :=
  let h := exists_place_over_two X
  X.pointedFieldOfModuli_eq_fieldOfModuli_of_normal h.choose_spec.1 ▸
    X.pointedModel (by norm_num) (by norm_num) h.choose_spec.1 h.choose_spec.2

/-- Every Galois Belyi covering over algebraically closed `k` is defined over its field of
moduli. -/
theorem IsoClass.isDefinedOver_fieldOfModuli_of_normal (X : AlgebraicBelyiPair k)
    [Normal (RatFunc k) X] : (IsoClass.mk X).IsDefinedOver (IsoClass.mk X).fieldOfModuli :=
  IsoClass.isDefinedOver_mk_iff.mpr ⟨modelOfNormal X⟩

end IsAlgClosed

end PointedDescent

end TauCeti.AlgebraicBelyiPair
