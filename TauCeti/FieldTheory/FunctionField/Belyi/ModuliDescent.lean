/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.FieldTheory.FunctionField.Belyi.CoefficientDescent
public import TauCeti.FieldTheory.FunctionField.Belyi.Model
import TauCeti.Algebra.Algebra.Equiv
import TauCeti.FieldTheory.FunctionField.Belyi.BaseChange
import TauCeti.FieldTheory.FunctionField.ConstantExtension.LinearDisjoint
import TauCeti.FieldTheory.FunctionField.Place.Degree
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import TauCeti.FieldTheory.FunctionField.Place.Extension.Galois
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Equiv
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
(`TauCeti.AlgebraicBelyiPair.pointedModel`) and deduces **Köck's Theorem 2.2**:

1. Because `[K(t)(z) : K(t)] = [F : k(t)]` and `K(t)(z) · k = F`, the subfield `K` is linearly
   disjoint from `K(t)(z)` over `K` (`TauCeti.linearDisjoint_fieldRange_of_finrank_ratFunc_eq`),
   with no algebraicity assumption on `k / K`.
2. Linearly disjoint base change (`TauCeti.isAlgebraicBelyiPair_iff_of_linearDisjoint`) therefore
   descends both exactness of the constant field and unramifiedness outside `{0, 1, ∞}` from
   `F / k(t)` to `K(t)(z) / K(t)`, making `K(t)(z)` a model of `X` over `K` of degree `d`.
3. When `k` is algebraically closed (such as `ℂ` or `AlgebraicClosure ℚ`), choosing any place `P`
   above `t = 2` yields a place of degree one whose pointed field of moduli has degree at most `d`
   over the field of moduli of `X`. Every isomorphism class `c` of Belyi pairs over `k` is thus
   defined over a finite extension of `c.fieldOfModuli` of degree at most `c.degree`
   (`TauCeti.AlgebraicBelyiPair.IsoClass.exists_finiteDimensional_and_isDefinedOver`, Köck's
   Theorem 2.2(a)).
4. When `F / k(t)` is Galois, deck automorphisms act transitively on the fibre over `t = q`, so
   every semilinear automorphism of `X` can be corrected by a deck automorphism to fix `P`. Hence
   `U(X, P) = U(X)` (`TauCeti.AlgebraicBelyiPair.pointedStabilizer_eq_stabilizer_of_isGalois`),
   `K` is the field of moduli itself, and over an algebraically closed field `X` is defined over
   its field of moduli (`TauCeti.AlgebraicBelyiPair.nonempty_model_fieldOfModuli_of_isGalois`,
   Köck's Theorem 2.2(b)).

## Main definitions

* `TauCeti.AlgebraicBelyiPair.pointedModel`: the model of `X` over `X.pointedFieldOfModuli P`
  attached to a degree-one place `P` over an unbranched rational point `t = q`.

## Main results

* `TauCeti.AlgebraicBelyiPair.finrank_pointedModel_pair`,
  `TauCeti.AlgebraicBelyiPair.nonempty_model_pointedFieldOfModuli`, and
  `TauCeti.AlgebraicBelyiPair.isDefinedOver_pointedFieldOfModuli`: properties of the pointed model.
* `TauCeti.AlgebraicBelyiPair.exists_relfinrank_le_finrank_and_nonempty_model`,
  `TauCeti.AlgebraicBelyiPair.IsoClass.exists_relfinrank_le_degree_and_isDefinedOver`, and
  `TauCeti.AlgebraicBelyiPair.IsoClass.exists_finiteDimensional_and_isDefinedOver`: **Köck's
  Theorem 2.2(a)**, every Belyi pair over an algebraically closed field of characteristic zero is
  defined over a finite extension of its field of moduli of degree at most the Belyi degree.
* `TauCeti.AlgebraicBelyiPair.pointedStabilizer_eq_stabilizer_of_isGalois` and
  `TauCeti.AlgebraicBelyiPair.pointedFieldOfModuli_eq_fieldOfModuli_of_isGalois`: for a Galois
  Belyi pair and a place over a rational point, the pointed stabilizer and pointed field of moduli
  agree with the unpointed ones.
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

omit [CharZero k] in
/-- If `z` generates `F` over `k(t)` and `E = K(t)⟮z⟯` contains `t`, then `E` and `k` generate
`F`. -/
private theorem adjoin_range_adjoin_simple_eq_top {K F : Type*} [Field K] [Field F]
    [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [Algebra (RatFunc K) F]
    (hX : algebraMap (RatFunc K) F RatFunc.X = algebraMap (RatFunc k) F RatFunc.X)
    {z : F} (hgen : (RatFunc k)⟮z⟯ = ⊤) :
    IntermediateField.adjoin k (Set.range (algebraMap (RatFunc K)⟮z⟯ F)) = ⊤ := by
  let L : IntermediateField k F :=
    IntermediateField.adjoin k (Set.range (algebraMap (RatFunc K)⟮z⟯ F))
  have hmemE : ∀ y : (RatFunc K)⟮z⟯, algebraMap (RatFunc K)⟮z⟯ F y ∈ L := fun y ↦
    IntermediateField.subset_adjoin k _ ⟨y, rfl⟩
  have hXmem : algebraMap (RatFunc k) F RatFunc.X ∈ L := by
    rw [← hX]
    exact hmemE (algebraMap (RatFunc K) (RatFunc K)⟮z⟯ RatFunc.X)
  have hpoly : ∀ p : k[X], algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) p) ∈ L :=
    fun p ↦ by
      rw [← RatFunc.aeval_X_left_eq_algebraMap, ← aeval_algebraMap_apply]
      refine Polynomial.induction_on' p (fun a b ha hb ↦ ?_) fun n a ↦ ?_
      · rw [map_add]
        exact L.add_mem ha hb
      · rw [aeval_monomial]
        exact L.mul_mem (L.algebraMap_mem a) (pow_mem hXmem n)
  have hrat : ∀ r : RatFunc k, algebraMap (RatFunc k) F r ∈ L := fun r ↦ by
    induction r using RatFunc.induction_on with
    | f p q _ =>
      rw [map_div₀]
      exact L.div_mem (hpoly p) (hpoly q)
  let L' : IntermediateField (RatFunc k) F :=
    { L.toSubfield with algebraMap_mem' := hrat }
  have hzL' : z ∈ L' := hmemE ⟨z, IntermediateField.mem_adjoin_simple_self _ z⟩
  have htop : L' = ⊤ := top_unique (hgen ▸ IntermediateField.adjoin_simple_le_iff.mpr hzL')
  exact eq_top_iff.mpr fun x _ ↦ show x ∈ L' from htop.symm ▸ trivial

variable (X : AlgebraicBelyiPair k)

/-- Auxiliary construction promoting a primitive element `z` of `X / k(t)` that is integral over
`K(t)` of full degree `[K(t)⟮z⟯ : K(t)] = [X : k(t)]` to a model of `X` over `K`. -/
private noncomputable def modelOfAdjoinSimple {K : Type u} [Field K] [CharZero K] [Algebra K k]
    [Algebra (RatFunc K) (RatFunc k)]
    [Algebra (RatFunc K) X] [IsScalarTower (RatFunc K) (RatFunc k) X]
    (hC : ∀ c : K,
      algebraMap (RatFunc K) (RatFunc k) (algebraMap K (RatFunc K) c) =
        algebraMap k (RatFunc k) (algebraMap K k c))
    (hX : algebraMap (RatFunc K) (RatFunc k) RatFunc.X = RatFunc.X)
    {z : X} (hgen : (RatFunc k)⟮z⟯ = ⊤) (hz_int : IsIntegral (RatFunc K) z)
    (hfinrank : Module.finrank (RatFunc K) (RatFunc K)⟮z⟯ = Module.finrank (RatFunc k) X) :
    { M : Model K X // Module.finrank (RatFunc K) M.pair = Module.finrank (RatFunc k) X } :=
  letI : Algebra K X := ((algebraMap k X).comp (algebraMap K k)).toAlgebra
  haveI : IsScalarTower K k X := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K (RatFunc K) X :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := RatFunc K) (A := X) fun c ↦ by
      rw [IsScalarTower.algebraMap_apply K k X,
        IsScalarTower.algebraMap_apply k (RatFunc k) X,
        ← hC c, ← IsScalarTower.algebraMap_apply (RatFunc K) (RatFunc k) X]
  let E : IntermediateField (RatFunc K) X := (RatFunc K)⟮z⟯
  letI : Algebra K E := ((algebraMap (RatFunc K) E).comp (algebraMap K (RatFunc K))).toAlgebra
  haveI : IsScalarTower K (RatFunc K) E := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K E X :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := E) (A := X) fun c ↦ by
      rw [IsScalarTower.algebraMap_apply K (RatFunc K) X,
        IsScalarTower.algebraMap_apply (RatFunc K) E X,
        ← IsScalarTower.algebraMap_apply K (RatFunc K) E]
  haveI : FiniteDimensional (RatFunc K) E := IntermediateField.adjoin.finiteDimensional hz_int
  have hX_E : algebraMap E X (algebraMap (RatFunc K) E RatFunc.X) =
      algebraMap (RatFunc k) X RatFunc.X := by
    rw [← IsScalarTower.algebraMap_apply (RatFunc K) E X,
      IsScalarTower.algebraMap_apply (RatFunc K) (RatFunc k) X, hX]
  have hadj : IntermediateField.adjoin k (Set.range (algebraMap E X)) = ⊤ :=
    adjoin_range_adjoin_simple_eq_top
      (by rw [IsScalarTower.algebraMap_apply (RatFunc K) (RatFunc k) X, hX]) hgen
  have hcomp : constantCompositum E k X = ⊤ :=
    constantCompositum_eq_top_of_adjoin_eq_top E k X hadj
  have H : (IsScalarTower.toAlgHom K k X).fieldRange.LinearDisjoint E :=
    linearDisjoint_fieldRange_of_finrank_ratFunc_eq hcomp hX_E hfinrank.symm
  have hembed : ∀ c : K,
      algebraMap E X (algebraMap K E c) = algebraMap k X (algebraMap K k c) := fun c ↦ by
    rw [← IsScalarTower.algebraMap_apply K E X, IsScalarTower.algebraMap_apply K k X]
  ⟨{ pair :=
      { carrier := E
        isAlgebraicBelyiPair :=
          (isAlgebraicBelyiPair_iff_of_linearDisjoint H hcomp hX_E).mp X.isAlgebraicBelyiPair }
     embedding := algebraMap E X
     embedding_algebraMap := hembed
     embedding_algebraMap_X := hX_E
     adjoin_range_embedding := hadj },
   hfinrank⟩

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
    rw [← RatFunc.algebraMap_eq_C, hC₀ c, RatFunc.algebraMap_eq_C]
    rfl
  have hX : algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k) RatFunc.X = RatFunc.X :=
    algebraMap_ratFuncAlgebraOfTranscendental_X hX_rf
  let h := X.exists_generator_finrank_adjoin_eq hq₀ hq₁ hPa hP hC hX
  X.modelOfAdjoinSimple hC₀ hX h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2.2

/-- **Pointed model descent**: at a place `P` of `X` of degree one over an unbranched rational
point `t = q` (`q ∈ ℚ \ {0, 1}`), the subfield `K(t)⟮z⟯` generated over
`K = X.pointedFieldOfModuli P` by a Laurent-normalized primitive element `z` is an algebraic Belyi
pair over `K` and a model of `X` over `K`. No algebraicity of `k / K` is required. -/
noncomputable def pointedModel {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) : Model (X.pointedFieldOfModuli P) X :=
  (X.pointedModelAux hq₀ hq₁ hPa hP).1

/-- The pointed model over `X.pointedFieldOfModuli P` has the same Belyi degree as `X`. -/
@[simp]
theorem finrank_pointedModel_pair {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) :
    Module.finrank (RatFunc (X.pointedFieldOfModuli P))
      (X.pointedModel hq₀ hq₁ hPa hP).pair = Module.finrank (RatFunc k) X :=
  (X.pointedModelAux hq₀ hq₁ hPa hP).2

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

/-- Over an algebraically closed field of characteristic zero, every algebraic Belyi pair has a
place of degree one over the unbranched rational point `t = 2`. -/
private theorem exists_place_over_two [IsAlgClosed k] (X : AlgebraicBelyiPair k) :
    ∃ P : Place k X,
      P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C ((2 : ℚ) : k)) ∧
      P.degree = 1 := by
  have hF : IsFunctionField k X := (IsFunctionField.ratFunc k).finite_extension
  obtain ⟨P, hPa⟩ := Place.restrict_surjective_of_finiteDimensional (IsFunctionField.ratFunc k) hF
    (Place.adicOfIrreducible (irreducible_X_sub_C ((2 : ℚ) : k)))
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
  obtain ⟨P, hPa, hP⟩ := exists_place_over_two X
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
theorem exists_finiteDimensional_and_isDefinedOver [IsAlgClosed k] (c : IsoClass k) :
    ∃ K : IntermediateField c.fieldOfModuli k,
      FiniteDimensional c.fieldOfModuli K ∧
      Module.finrank c.fieldOfModuli K ≤ c.degree ∧
      c.IsDefinedOver K := by
  obtain ⟨K₀, hle, hpos, hdeg, hc⟩ := c.exists_relfinrank_le_degree_and_isDefinedOver
  let K : IntermediateField c.fieldOfModuli k :=
    { K₀.toSubfield with algebraMap_mem' := fun m ↦ hle m.2 }
  have hfinrank : Module.finrank c.fieldOfModuli K = c.fieldOfModuli.relfinrank K₀ :=
    (IntermediateField.relfinrank_eq_finrank_of_le hle).symm
  have : FiniteDimensional c.fieldOfModuli K :=
    FiniteDimensional.of_finrank_pos (hfinrank ▸ hpos)
  exact ⟨K, inferInstance, hfinrank ▸ hdeg, hc⟩

end IsoClass

end AlgClosed

/-! ### Köck's Theorem 2.2(b): Galois Belyi pairs descend to the field of moduli -/

section Galois

variable (X : AlgebraicBelyiPair k) [IsGalois (RatFunc k) X]

/-- **For a Galois Belyi pair, the pointed stabilizer at any place over a rational point equals the
full stabilizer of the isomorphism class.** Any semilinear automorphism moves `P` to another place
in the same rational fibre, and Galois transitivity over `k(t)` restores `P`. -/
theorem pointedStabilizer_eq_stabilizer_of_isGalois {P : Place k X} {q : ℚ}
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k))) :
    X.pointedStabilizer P = MulAction.stabilizer (k ≃ₐ[ℚ] k) (IsoClass.mk X) := by
  refine le_antisymm (X.pointedStabilizer_le_stabilizer P) fun g hg ↦ ?_
  rw [← X.map_snd_semilinearAut, Subgroup.mem_map] at hg
  obtain ⟨p, hp, hpg⟩ := hg
  have hfib : ((⟨p, hp⟩ : X.semilinearAut) • P).restrict k (RatFunc k) =
      P.restrict k (RatFunc k) := by
    rw [restrict_smul, hPa, Place.equivOfRingEquiv_mapRingEquiv_adicOfIrreducible_X_sub_C,
      map_ratCast]
  obtain ⟨σ, hσ⟩ := Place.exists_smul_eq_of_restrict_eq hfib
  have hs : (σ.toRingEquiv, (1 : k ≃ₐ[ℚ] k)) ∈ X.semilinearAut :=
    mem_semilinearAut_iff.mpr fun r ↦ by
      rw [AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes, AlgEquiv.toRingEquiv_one,
        RatFunc.mapRingEquiv_refl, RingEquiv.refl_apply]
  let s : X.semilinearAut := ⟨(σ.toRingEquiv, 1), hs⟩
  have hs_smul : ∀ Q : Place k X, s • Q = σ • Q := fun Q ↦
    Place.ext <| Valuation.ext fun z ↦ by
      rw [valuation_smul, Place.valuation_smul]
      rfl
  rw [pointedStabilizer_def, Subgroup.mem_map]
  refine ⟨s * ⟨p, hp⟩, ?_, ?_⟩
  · change (s * ⟨p, hp⟩) • P = P
    rw [mul_smul, hs_smul, hσ]
  · simpa [s] using hpg

/-- **For a Galois Belyi pair, the pointed field of moduli at any place over a rational point is
the field of moduli of the pair.** -/
theorem pointedFieldOfModuli_eq_fieldOfModuli_of_isGalois {P : Place k X} {q : ℚ}
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k))) :
    X.pointedFieldOfModuli P = (IsoClass.mk X).fieldOfModuli := by
  rw [pointedFieldOfModuli_def, IsoClass.fieldOfModuli_def,
    X.pointedStabilizer_eq_stabilizer_of_isGalois hPa]

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
  obtain ⟨P, hPa, hP⟩ := exists_place_over_two X
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
