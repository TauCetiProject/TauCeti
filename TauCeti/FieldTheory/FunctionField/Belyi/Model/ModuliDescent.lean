/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.CoefficientDescent
public import TauCeti.FieldTheory.FunctionField.Belyi.Model.Basic
import TauCeti.FieldTheory.FunctionField.Belyi.Model.AdjoinSimple
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Descent of Belyi pairs to the pointed field of moduli

Let `X = (F, k(t) ↪ F)` be an algebraic Belyi pair of degree `d` over a field `k` of characteristic
zero — possibly transcendental over `ℚ`, such as `ℂ` — and let `P` be a place of `F` of degree one
lying over an unbranched rational point `t = q` (`q ∈ ℚ \ {0, 1}`). In
`TauCeti.FieldTheory.FunctionField.Belyi.CoefficientDescent` a Laurent-normalized primitive element
`z` of `F / k(t)` at `P` was shown to have minimal polynomial over `k(t)` with coefficients in
`K(t)`, where `K = X.pointedFieldOfModuli P` is the fixed field of the pointed stabilizer
`U(X, P) ≤ Aut(k)`.

This file promotes that descended equation to a genuine **model** of `X` over `K`
(`TauCeti.AlgebraicBelyiPair.pointedModel`) via `TauCeti.AlgebraicBelyiPair.modelOfAdjoinSimple`
and deduces **Köck's Theorem 2.2**:

1. Because `[K(t)(z) : K(t)] = [F : k(t)]` and `K(t)(z) · k = F`, the image of `k` is linearly
   disjoint from `K(t)(z)` over `K` (`TauCeti.linearDisjoint_of_finrank_ratFunc_eq`),
   with no algebraicity assumption on `k / K`.
2. Degree-preserving base-change descent (`TauCeti.IsAlgebraicBelyiPair.of_finrank_eq`, via
   `TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`) therefore descends both
   exactness of the constant field and unramifiedness outside `{0, 1, ∞}` from `F / k(t)` to
   `K(t)(z) / K(t)`, making `K(t)(z)` a model of `X` over `K` of degree `d`.
3. When `k` is algebraically closed (such as `ℂ` or `AlgebraicClosure ℚ`), choosing any place `P`
   above `t = 2` yields a place of degree one whose pointed field of moduli has degree at most `d`
   over the field of moduli of `X`. Every isomorphism class `c` of Belyi pairs over `k` is thus
   defined over a finite extension of `c.fieldOfModuli` of degree at most `c.degree`
   (`TauCeti.AlgebraicBelyiPair.IsoClass.exists_finrank_le_degree_and_isDefinedOver`, Köck's
   Theorem 2.2(a)).
4. When `F / k(t)` is Galois, `U(X, P) = U(X)`
   (`TauCeti.AlgebraicBelyiPair.pointedStabilizer_eq_stabilizer_of_isGalois`), so `K` is the field
   of moduli itself
   (`TauCeti.AlgebraicBelyiPair.pointedFieldOfModuli_eq_fieldOfModuli_of_isGalois`), and over an
   algebraically closed field `X` is defined over its field of moduli
   (`TauCeti.AlgebraicBelyiPair.nonempty_model_fieldOfModuli_of_isGalois`, Köck's Theorem 2.2(b)).

## Main definitions

* `TauCeti.AlgebraicBelyiPair.pointedModel`: the model of `X` over `X.pointedFieldOfModuli P`
  attached to a degree-one place `P` over an unbranched rational point `t = q`.

## Main results

* `TauCeti.AlgebraicBelyiPair.finrank_pointedModel_pair`,
  `TauCeti.AlgebraicBelyiPair.nonempty_model_pointedFieldOfModuli`, and
  `TauCeti.AlgebraicBelyiPair.isDefinedOver_pointedFieldOfModuli`: properties of the pointed model.
* `TauCeti.AlgebraicBelyiPair.exists_relfinrank_le_finrank_and_nonempty_model`,
  `TauCeti.AlgebraicBelyiPair.IsoClass.exists_relfinrank_le_degree_and_isDefinedOver`, and
  `TauCeti.AlgebraicBelyiPair.IsoClass.exists_finrank_le_degree_and_isDefinedOver`: **Köck's
  Theorem 2.2(a)**, every Belyi pair over an algebraically closed field of characteristic zero is
  defined over a finite extension of its field of moduli of degree at most the Belyi degree.
* `TauCeti.AlgebraicBelyiPair.nonempty_model_fieldOfModuli_of_isGalois` and
  `TauCeti.AlgebraicBelyiPair.IsoClass.isDefinedOver_fieldOfModuli_of_isGalois`: **Köck's
  Theorem 2.2(b)**, every Galois Belyi pair over an algebraically closed field of characteristic
  zero is defined over its field of moduli.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  (2.2) Theorem.
-/

public section

universe u

open Polynomial IntermediateField

namespace TauCeti.AlgebraicBelyiPair

variable {k : Type u} [Field k] [CharZero k]

section PointedModel

variable (X : AlgebraicBelyiPair k)

/-- Auxiliary packaging of the pointed model together with its degree over `K(t)`. -/
private noncomputable def pointedModelAux {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) :
    { M : Model (X.pointedFieldOfModuli P) X //
      Module.finrank (RatFunc (X.pointedFieldOfModuli P)) M.pair =
        Module.finrank (RatFunc k) X } :=
  have hX_rf : Transcendental (X.pointedFieldOfModuli P) (RatFunc.X : RatFunc k) :=
    RatFunc.transcendental_X.of_tower_top (X.pointedFieldOfModuli P)
  letI : Algebra (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k) :=
    ratFuncAlgebraOfTranscendental hX_rf
  haveI : IsScalarTower (X.pointedFieldOfModuli P) (RatFunc (X.pointedFieldOfModuli P))
      (RatFunc k) :=
    isScalarTower_ratFuncAlgebraOfTranscendental hX_rf
  letI : Algebra (RatFunc (X.pointedFieldOfModuli P)) X :=
    ((algebraMap (RatFunc k) X).comp
      (algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k))).toAlgebra
  haveI : IsScalarTower (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k) X :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hC₀ : ∀ c : X.pointedFieldOfModuli P,
      algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k)
        (algebraMap (X.pointedFieldOfModuli P) (RatFunc (X.pointedFieldOfModuli P)) c) =
        algebraMap k (RatFunc k) (algebraMap (X.pointedFieldOfModuli P) k c) := fun c ↦ by
    rw [← IsScalarTower.algebraMap_apply (X.pointedFieldOfModuli P)
        (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k),
      IsScalarTower.algebraMap_apply (X.pointedFieldOfModuli P) k (RatFunc k)]
  have hC : ∀ c : X.pointedFieldOfModuli P,
      algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k) (RatFunc.C c) =
        RatFunc.C (c : k) := fun c ↦ by
    rw [← RatFunc.algebraMap_eq_C, hC₀ c, RatFunc.algebraMap_eq_C,
      IntermediateField.algebraMap_apply]
  have hX : algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k) RatFunc.X = RatFunc.X :=
    algebraMap_ratFuncAlgebraOfTranscendental_X hX_rf
  let h := X.exists_generator_finrank_adjoin_eq hq₀ hq₁ hPa hP hC hX
  ⟨X.modelOfAdjoinSimple hC₀ hX h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2.2,
    finrank_modelOfAdjoinSimple_pair X _ _ _ _ _⟩

/-- **Pointed model descent**: at a place `P` of `X` of degree one over an unbranched rational
point `t = q` (`q ∈ ℚ \ {0, 1}`), `X` admits a model over `X.pointedFieldOfModuli P`. No
algebraicity of `k / X.pointedFieldOfModuli P` is required. -/
noncomputable def pointedModel {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) : Model (X.pointedFieldOfModuli P) X :=
  (X.pointedModelAux hq₀ hq₁ hPa hP).val

/-- The pointed model over `X.pointedFieldOfModuli P` has the same Belyi degree as `X`. -/
@[simp]
theorem finrank_pointedModel_pair {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) :
    Module.finrank (RatFunc (X.pointedFieldOfModuli P))
      (X.pointedModel hq₀ hq₁ hPa hP).pair = Module.finrank (RatFunc k) X :=
  (X.pointedModelAux hq₀ hq₁ hPa hP).property

/-- Every algebraic Belyi pair admitting a degree-one place over an unbranched rational point has a
model over its pointed field of moduli at that place. -/
theorem nonempty_model_pointedFieldOfModuli {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) :
    Nonempty (Model (X.pointedFieldOfModuli P) X) :=
  ⟨X.pointedModel hq₀ hq₁ hPa hP⟩

/-- The isomorphism class of a pair admitting a degree-one place over an unbranched rational point
is defined over its pointed field of moduli at that place. -/
theorem isDefinedOver_pointedFieldOfModuli {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) :
    (IsoClass.mk X).IsDefinedOver (X.pointedFieldOfModuli P) :=
  IsoClass.isDefinedOver_mk_iff.mpr (X.nonempty_model_pointedFieldOfModuli hq₀ hq₁ hPa hP)

end PointedModel

/-! ### Köck's Theorem 2.2(a): descent to a bounded extension of the field of moduli -/

section AlgClosed

/-- **Köck's Theorem 2.2(a), pair form**: over an algebraically closed field `k` of characteristic
zero (such as `ℂ` or `AlgebraicClosure ℚ`), every algebraic Belyi pair `X` has a model over a
finite extension `K` of its field of moduli inside `k` of degree at most `[X : k(t)]`. -/
theorem exists_relfinrank_le_finrank_and_nonempty_model [IsAlgClosed k]
    (X : AlgebraicBelyiPair k) :
    ∃ K : IntermediateField ℚ k,
      (IsoClass.mk X).fieldOfModuli ≤ K ∧
      0 < (IsoClass.mk X).fieldOfModuli.relfinrank K ∧
      (IsoClass.mk X).fieldOfModuli.relfinrank K ≤ Module.finrank (RatFunc k) X ∧
      Nonempty (Model K X) := by
  obtain ⟨P, hPa, hP⟩ := Place.exists_restrict_eq_and_degree_eq_one_of_finiteDimensional (F' := X)
    (IsFunctionField.ratFunc k) (IsFunctionField.ratFunc k).finite_extension
    (Place.adicOfIrreducible (irreducible_X_sub_C ((2 : ℚ) : k)))
  exact ⟨X.pointedFieldOfModuli P, X.fieldOfModuli_le_pointedFieldOfModuli P,
    X.relfinrank_pointedFieldOfModuli_pos hPa, X.relfinrank_pointedFieldOfModuli_le hPa,
    X.nonempty_model_pointedFieldOfModuli (q := 2) (by norm_num) (by norm_num) hPa hP⟩

namespace IsoClass

/-- Over an algebraically closed field `k` of characteristic zero, every isomorphism class `c` of
algebraic Belyi pairs is defined over an intermediate field `K` of `k / ℚ` that is a finite
extension of `c.fieldOfModuli` of relative degree at most `c.degree`. -/
theorem exists_relfinrank_le_degree_and_isDefinedOver [IsAlgClosed k] (c : IsoClass k) :
    ∃ K : IntermediateField ℚ k,
      c.fieldOfModuli ≤ K ∧
      0 < c.fieldOfModuli.relfinrank K ∧
      c.fieldOfModuli.relfinrank K ≤ c.degree ∧
      c.IsDefinedOver K := by
  induction c using ind with
  | h X =>
    obtain ⟨K, hle, hpos, hdeg, hM⟩ := X.exists_relfinrank_le_finrank_and_nonempty_model
    exact ⟨K, hle, hpos, by simpa using hdeg, isDefinedOver_mk_iff.mpr hM⟩

/-- **Köck's Theorem 2.2(a)**: over an algebraically closed field `k` of characteristic zero, every
isomorphism class `c` of algebraic Belyi pairs is defined over a finite extension `K` of its field
of moduli `c.fieldOfModuli` inside `k` with `[K : c.fieldOfModuli] ≤ c.degree`. -/
theorem exists_finrank_le_degree_and_isDefinedOver [IsAlgClosed k] (c : IsoClass k) :
    ∃ K : IntermediateField c.fieldOfModuli k,
      FiniteDimensional c.fieldOfModuli K ∧
      Module.finrank c.fieldOfModuli K ≤ c.degree ∧
      c.IsDefinedOver K := by
  obtain ⟨K₀, hle, hpos, hdeg, hc⟩ := c.exists_relfinrank_le_degree_and_isDefinedOver
  let K : IntermediateField c.fieldOfModuli k := IntermediateField.extendScalars hle
  have hfinrank : Module.finrank c.fieldOfModuli K = c.fieldOfModuli.relfinrank K₀ :=
    (IntermediateField.relfinrank_eq_finrank_of_le hle).symm
  have : FiniteDimensional c.fieldOfModuli K :=
    FiniteDimensional.of_finrank_pos (hfinrank ▸ hpos)
  -- `extendScalars hle` shares the exact `Subfield` carrier and `k`-algebra map of `K₀`.
  exact ⟨K, inferInstance, hfinrank ▸ hdeg, hc⟩

end IsoClass

end AlgClosed

/-! ### Köck's Theorem 2.2(b): Galois Belyi pairs descend to the field of moduli -/

section Galois

variable (X : AlgebraicBelyiPair k) [IsGalois (RatFunc k) X]

/-- A Galois Belyi pair admitting a degree-one place over an unbranched rational point has a model
over its field of moduli. -/
theorem nonempty_model_fieldOfModuli_of_degree_eq_one_of_isGalois {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) :
    Nonempty (Model (IsoClass.mk X).fieldOfModuli X) := by
  rw [← X.pointedFieldOfModuli_eq_fieldOfModuli_of_isGalois hPa]
  exact X.nonempty_model_pointedFieldOfModuli hq₀ hq₁ hPa hP

/-- **Köck's Theorem 2.2(b), model form**: over an algebraically closed field `k` of characteristic
zero (such as `ℂ` or `AlgebraicClosure ℚ`), every Galois algebraic Belyi pair `X` has a model over
its field of moduli. -/
theorem nonempty_model_fieldOfModuli_of_isGalois [IsAlgClosed k] :
    Nonempty (Model (IsoClass.mk X).fieldOfModuli X) := by
  obtain ⟨P, hPa, hP⟩ := Place.exists_restrict_eq_and_degree_eq_one_of_finiteDimensional (F' := X)
    (IsFunctionField.ratFunc k) (IsFunctionField.ratFunc k).finite_extension
    (Place.adicOfIrreducible (irreducible_X_sub_C ((2 : ℚ) : k)))
  exact X.nonempty_model_fieldOfModuli_of_degree_eq_one_of_isGalois
    (q := 2) (by norm_num) (by norm_num) hPa hP

/-- **Köck's Theorem 2.2(b)**: over an algebraically closed field `k` of characteristic zero, the
isomorphism class of every Galois algebraic Belyi pair is defined over its field of moduli. -/
theorem _root_.TauCeti.AlgebraicBelyiPair.IsoClass.isDefinedOver_fieldOfModuli_of_isGalois
    [IsAlgClosed k] :
    (IsoClass.mk X).IsDefinedOver (IsoClass.mk X).fieldOfModuli :=
  IsoClass.isDefinedOver_mk_iff.mpr X.nonempty_model_fieldOfModuli_of_isGalois

end Galois

end TauCeti.AlgebraicBelyiPair
