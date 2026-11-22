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
lying over a finite rational point `t = q` with `q ≠ 0, 1`. In
`TauCeti.FieldTheory.FunctionField.Belyi.CoefficientDescent` a Laurent-normalized primitive element
`z` of `F / k(t)` at `P` was shown to have minimal polynomial over `k(t)` with coefficients in
`K(t)`, where `K = X.pointedFieldOfModuli P` is the fixed field of the pointed stabilizer
`U(X, P) ≤ Aut(k)`.

This file promotes that descended equation to a genuine **model** of `X` over `K`
(`TauCeti.AlgebraicBelyiPair.modelOverPointedFieldOfModuli`) via
`TauCeti.AlgebraicBelyiPair.modelOfAdjoinSimple` and deduces **Köck's Theorem 2.2**:

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

* `TauCeti.AlgebraicBelyiPair.modelOverPointedFieldOfModuli`: a model of `X` over
  `X.pointedFieldOfModuli P` attached to a degree-one place `P` over a finite rational point
  `t = q` with `q ≠ 0, 1`.

## Main results

* `TauCeti.AlgebraicBelyiPair.finrank_modelOverPointedFieldOfModuli_pair`,
  `TauCeti.AlgebraicBelyiPair.exists_generator_fieldRange_modelOverPointedFieldOfModuli`,
  `TauCeti.AlgebraicBelyiPair.nonempty_model_pointedFieldOfModuli`, and
  `TauCeti.AlgebraicBelyiPair.isDefinedOver_pointedFieldOfModuli`: properties of the model over the
  pointed field of moduli.
* `TauCeti.AlgebraicBelyiPair.exists_relfinrank_le_finrank_and_nonempty_model` and
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

/-- Auxiliary packaging of the model over `X.pointedFieldOfModuli P` together with its degree and
defining generator over `K(t)`. -/
private noncomputable def modelOverPointedFieldOfModuliAux {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) :
    letI : Algebra (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k) :=
      ratFuncAlgebraOfTranscendental (RatFunc.transcendental_X.of_tower_top _)
    letI : Algebra (RatFunc (X.pointedFieldOfModuli P)) X :=
      ((algebraMap (RatFunc k) X).comp
        (algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k))).toAlgebra
    { M : Model (X.pointedFieldOfModuli P) X //
      Module.finrank (RatFunc (X.pointedFieldOfModuli P)) M.pair =
        Module.finrank (RatFunc k) X ∧
      ∃ z : X, (RatFunc k)⟮z⟯ = ⊤ ∧
        IsIntegral (RatFunc (X.pointedFieldOfModuli P)) z ∧
        (minpoly (RatFunc (X.pointedFieldOfModuli P)) z).map
          (algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k)) = minpoly (RatFunc k) z ∧
        M.embedding.fieldRange = ((RatFunc (X.pointedFieldOfModuli P))⟮z⟯).toSubfield } :=
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
  ⟨X.modelOfAdjoinSimple hC₀ hX h.choose_spec.1 h.choose_spec.2.2.2,
    finrank_modelOfAdjoinSimple_pair X _ _ _ _,
    ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2.1,
      X.fieldRange_modelOfAdjoinSimple_embedding hC₀ hX h.choose_spec.1 h.choose_spec.2.2.2⟩⟩

/-- **Pointed-field model descent**: at a place `P` of `X` of degree one over a finite rational
point `t = q` with `q ≠ 0, 1`, `X` admits a model over `X.pointedFieldOfModuli P`. No algebraicity
of `k / X.pointedFieldOfModuli P` is required. -/
noncomputable def modelOverPointedFieldOfModuli {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) : Model (X.pointedFieldOfModuli P) X :=
  (X.modelOverPointedFieldOfModuliAux hq₀ hq₁ hPa hP).val

/-- The model over `X.pointedFieldOfModuli P` has the same Belyi degree as `X`. -/
@[simp]
theorem finrank_modelOverPointedFieldOfModuli_pair {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) :
    Module.finrank (RatFunc (X.pointedFieldOfModuli P))
      (X.modelOverPointedFieldOfModuli hq₀ hq₁ hPa hP).pair = Module.finrank (RatFunc k) X :=
  (X.modelOverPointedFieldOfModuliAux hq₀ hq₁ hPa hP).property.1

/-- The embedding image of `X.modelOverPointedFieldOfModuli hq₀ hq₁ hPa hP` is `K(t)⟮z⟯` for a
primitive element `z` of `X / k(t)` whose minimal polynomial over `k(t)` descends to `K(t)`, where
`K = X.pointedFieldOfModuli P`. -/
theorem exists_generator_fieldRange_modelOverPointedFieldOfModuli {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1)
    [inst₁ : Algebra (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k)]
    [inst₂ : Algebra (RatFunc (X.pointedFieldOfModuli P)) X]
    [IsScalarTower (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k) X]
    (hC : ∀ c : X.pointedFieldOfModuli P,
      algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k) (RatFunc.C c) =
        RatFunc.C (c : k))
    (hX : algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k) RatFunc.X = RatFunc.X) :
    ∃ z : X, (RatFunc k)⟮z⟯ = ⊤ ∧
      IsIntegral (RatFunc (X.pointedFieldOfModuli P)) z ∧
      (minpoly (RatFunc (X.pointedFieldOfModuli P)) z).map
        (algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k)) = minpoly (RatFunc k) z ∧
      (X.modelOverPointedFieldOfModuli hq₀ hq₁ hPa hP).embedding.fieldRange =
        ((RatFunc (X.pointedFieldOfModuli P))⟮z⟯).toSubfield := by
  have hX_rf : Transcendental (X.pointedFieldOfModuli P) (RatFunc.X : RatFunc k) :=
    RatFunc.transcendental_X.of_tower_top (X.pointedFieldOfModuli P)
  have hinst₁ : inst₁ = ratFuncAlgebraOfTranscendental hX_rf := by
    refine Algebra.algebra_ext _ _ fun r ↦ RingHom.congr_fun ?_ r
    refine IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial (X.pointedFieldOfModuli P))) ?_
    refine Polynomial.ringHom_ext' ?_ ?_
    · ext c
      simp only [RingHom.comp_apply, RatFunc.algebraMap_C, hC c]
      let _ := ratFuncAlgebraOfTranscendental hX_rf
      have htower := isScalarTower_ratFuncAlgebraOfTranscendental hX_rf
      rw [← RatFunc.algebraMap_eq_C (K := k),
        ← RatFunc.algebraMap_eq_C (K := X.pointedFieldOfModuli P),
        ← IntermediateField.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply (X.pointedFieldOfModuli P) k (RatFunc k),
        IsScalarTower.algebraMap_apply (X.pointedFieldOfModuli P)
          (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k)]
    · simp only [RingHom.comp_apply, RatFunc.algebraMap_X, hX]
      exact (algebraMap_ratFuncAlgebraOfTranscendental_X hX_rf).symm
  have hinst₂ : inst₂ = ((algebraMap (RatFunc k) X).comp
      (algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k))).toAlgebra :=
    Algebra.algebra_ext _ _ fun r ↦
      IsScalarTower.algebraMap_apply (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k) X r
  subst hinst₁
  subst hinst₂
  exact (X.modelOverPointedFieldOfModuliAux hq₀ hq₁ hPa hP).property.2

/-- Every algebraic Belyi pair admitting a degree-one place over a finite rational point `t = q`
with `q ≠ 0, 1` has a model over its pointed field of moduli at that place. -/
theorem nonempty_model_pointedFieldOfModuli {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) :
    Nonempty (Model (X.pointedFieldOfModuli P) X) :=
  ⟨X.modelOverPointedFieldOfModuli hq₀ hq₁ hPa hP⟩

/-- The isomorphism class of a pair admitting a degree-one place over a finite rational point
`t = q` with `q ≠ 0, 1` is defined over its pointed field of moduli at that place. -/
theorem isDefinedOver_pointedFieldOfModuli {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) :
    (IsoClass.mk X).IsDefinedOver (X.pointedFieldOfModuli P) :=
  IsoClass.isDefinedOver_mk_iff.mpr (X.nonempty_model_pointedFieldOfModuli hq₀ hq₁ hPa hP)

end PointedModel

/-! ### Köck's Theorem 2.2(a): descent to a bounded extension of the field of moduli -/

section AlgClosed

private theorem exists_place_over_two_and_degree_eq_one [IsAlgClosed k]
    (X : AlgebraicBelyiPair k) :
    ∃ P : Place k X,
      P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C ((2 : ℚ) : k)) ∧
      P.degree = 1 := by
  have hF : IsFunctionField k X := (IsFunctionField.ratFunc k).finite_extension
  obtain ⟨P, hPa⟩ := Place.restrict_surjective_of_finiteDimensional
    (IsFunctionField.ratFunc k) hF (Place.adicOfIrreducible (irreducible_X_sub_C ((2 : ℚ) : k)))
  exact ⟨P, hPa, P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF⟩

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
  obtain ⟨P, hPa, hP⟩ := exists_place_over_two_and_degree_eq_one X
  exact ⟨X.pointedFieldOfModuli P, X.fieldOfModuli_le_pointedFieldOfModuli P,
    X.relfinrank_pointedFieldOfModuli_pos hPa, X.relfinrank_pointedFieldOfModuli_le hPa,
    X.nonempty_model_pointedFieldOfModuli (q := 2) (by norm_num) (by norm_num) hPa hP⟩

namespace IsoClass

/-- **Köck's Theorem 2.2(a)**: over an algebraically closed field `k` of characteristic zero, every
isomorphism class `c` of algebraic Belyi pairs is defined over a finite extension `K` of its field
of moduli `c.fieldOfModuli` inside `k` with `[K : c.fieldOfModuli] ≤ c.degree`. -/
theorem exists_finrank_le_degree_and_isDefinedOver [IsAlgClosed k] (c : IsoClass k) :
    ∃ K : IntermediateField c.fieldOfModuli k,
      FiniteDimensional c.fieldOfModuli K ∧
      Module.finrank c.fieldOfModuli K ≤ c.degree ∧
      c.IsDefinedOver K := by
  induction c using ind with
  | h X =>
    obtain ⟨K₀, hle, hpos, hdeg, hM⟩ := X.exists_relfinrank_le_finrank_and_nonempty_model
    let K : IntermediateField (mk X).fieldOfModuli k := IntermediateField.extendScalars hle
    have hfinrank : Module.finrank (mk X).fieldOfModuli K = (mk X).fieldOfModuli.relfinrank K₀ :=
      (IntermediateField.relfinrank_eq_finrank_of_le hle).symm
    have : FiniteDimensional (mk X).fieldOfModuli K :=
      FiniteDimensional.of_finrank_pos (hfinrank ▸ hpos)
    -- `extendScalars hle` shares the exact `Subfield` carrier and `k`-algebra map of `K₀`.
    exact ⟨K, inferInstance, hfinrank ▸ by simpa using hdeg, isDefinedOver_mk_iff.mpr hM⟩

end IsoClass

end AlgClosed

/-! ### Köck's Theorem 2.2(b): Galois Belyi pairs descend to the field of moduli -/

section Galois

variable (X : AlgebraicBelyiPair k) [IsGalois (RatFunc k) X]

/-- A Galois Belyi pair admitting a degree-one place over a finite rational point `t = q` with
`q ≠ 0, 1` has a model over its field of moduli. -/
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
  obtain ⟨P, hPa, hP⟩ := exists_place_over_two_and_degree_eq_one X
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
