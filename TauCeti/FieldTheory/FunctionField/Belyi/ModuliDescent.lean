/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.CoefficientDescent
public import TauCeti.FieldTheory.FunctionField.Belyi.Model
import TauCeti.FieldTheory.FunctionField.Belyi.BaseChange
import TauCeti.FieldTheory.FunctionField.ConstantExtension.MinpolyDescent
import TauCeti.FieldTheory.FunctionField.ConstantExtension.RatFunc
import TauCeti.FieldTheory.FunctionField.Place.Degree
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import TauCeti.FieldTheory.FunctionField.Place.Extension.Galois
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Equiv
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# Descent of algebraic Belyi pairs to pointed fields of moduli

Let `X = (F, k(t) ↪ F)` be an algebraic Belyi pair over a field `k` of characteristic zero, such as
`ℂ` or `AlgebraicClosure ℚ`. At any rational unbranched place `P` of `F` of degree one — for
instance any place over `t = 2` when `k` is algebraically closed — the Laurent-normalized primitive
element `z` of `F / k(t)` constructed in
`TauCeti.FieldTheory.FunctionField.Belyi.CoefficientDescent` has minimal polynomial with
coefficients in `K(t)`, where `K = k ^ U(X, P)` is the pointed field of moduli
`TauCeti.AlgebraicBelyiPair.pointedFieldOfModuli`.

Combining minimal-polynomial descent of exact constants
(`TauCeti.isIntegrallyClosedIn_adjoin_simple_ratFunc_of_minpoly_mem_lifts`) with the arbitrary
constant-extension comparison for Belyi pairs
(`TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`) upgrades that descended equation
to an actual `TauCeti.AlgebraicBelyiPair.Model` of `X` over `K`. No algebraicity of `k / K` is
assumed, so the construction applies directly to `k = ℂ`, where `ℂ / K` has continuum transcendence
degree.

This proves Köck's Theorem 2.2:
* Over any algebraically closed field `k` of characteristic zero, every algebraic Belyi pair `X` has
  a model over a finite extension `K` of its field of moduli `M(X)` of relative degree at most
  `[F : k(t)]` (`TauCeti.AlgebraicBelyiPair.exists_model_relfinrank_le`). Whenever `M(X)` is finite
  over `ℚ`, `K` is a number field of degree at most `[M(X) : ℚ] · [F : k(t)]`
  (`TauCeti.AlgebraicBelyiPair.exists_model_of_finiteDimensional_fieldOfModuli`).
* When `F / k(t)` is Galois, `Gal(F / k(t))` acts transitively on the fibre over `t = q`, so every
  semilinear automorphism of `X` can be composed with a deck transformation to fix `P`. Thus
  `U(X, P) = U(X)`, `K = M(X)`, and `X` is defined over its field of moduli `M(X)` itself
  (`TauCeti.AlgebraicBelyiPair.modelOfIsGalois`,
  `TauCeti.AlgebraicBelyiPair.IsoClass.isDefinedOver_fieldOfModuli_of_isGalois`).

## Main definitions

* `TauCeti.AlgebraicBelyiPair.modelOfMinpolyMemLifts`: the model `K(t)(z)` of `X` over `K` attached
  to a generator `z` of `X / k(t)` whose minimal polynomial lifts to `K(t)`.
* `TauCeti.AlgebraicBelyiPair.modelOfMinpolyMemLiftsGen`: the distinguished generator of
  `modelOfMinpolyMemLifts` corresponding to `z`.
* `TauCeti.AlgebraicBelyiPair.modelOfMinpolyMemLiftsEquiv`: canonical `K(t)`-algebra isomorphism
  identifying the function field of `modelOfMinpolyMemLifts` with the subfield `K(t)(z)` of `X`.
* `TauCeti.AlgebraicBelyiPair.pointedModel`: the model of `X` over `X.pointedFieldOfModuli P` at a
  rational unbranched place `P` of degree one.
* `TauCeti.AlgebraicBelyiPair.modelOfIsGalois`: over an algebraically closed field `k`, a model of a
  Galois Belyi pair `X` over its field of moduli.

## Main results

* `TauCeti.AlgebraicBelyiPair.embedding_modelOfMinpolyMemLifts_algebraMap_ratFunc`,
  `TauCeti.AlgebraicBelyiPair.embedding_modelOfMinpolyMemLiftsGen`,
  `TauCeti.AlgebraicBelyiPair.adjoin_modelOfMinpolyMemLiftsGen`,
  `TauCeti.AlgebraicBelyiPair.map_minpoly_modelOfMinpolyMemLiftsGen`, and
  `TauCeti.AlgebraicBelyiPair.range_embedding_modelOfMinpolyMemLifts`: characteristic API for
  `modelOfMinpolyMemLifts` without unfolding its definition.
* `TauCeti.AlgebraicBelyiPair.isDefinedOver_pointedFieldOfModuli`: the class of `X` is defined over
  `X.pointedFieldOfModuli P`.
* `TauCeti.AlgebraicBelyiPair.exists_model_relfinrank_le` and
  `TauCeti.AlgebraicBelyiPair.IsoClass.exists_isDefinedOver_relfinrank_le`: **Köck, Theorem 2.2** —
  over an algebraically closed field of characteristic zero, every Belyi pair is defined over a
  finite extension of its field of moduli of degree at most the degree of the cover.
* `TauCeti.AlgebraicBelyiPair.exists_model_of_finiteDimensional_fieldOfModuli` and
  `TauCeti.AlgebraicBelyiPair.IsoClass.exists_isDefinedOver_of_finiteDimensional_fieldOfModuli`:
  consequence when the field of moduli is a number field.
* `TauCeti.AlgebraicBelyiPair.pointedStabilizer_eq_stabilizer_of_isGalois` and
  `TauCeti.AlgebraicBelyiPair.pointedFieldOfModuli_eq_fieldOfModuli_of_isGalois`: for a Galois
  Belyi pair, the pointed stabilizer and pointed field of moduli at a rational place agree with the
  full stabilizer and field of moduli.
* `TauCeti.AlgebraicBelyiPair.IsoClass.isDefinedOver_fieldOfModuli_of_isGalois`: **Köck,
  Theorem 2.2 (Galois case)** — over an algebraically closed field of characteristic zero, every
  Galois Belyi pair is defined over its field of moduli.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  (2.2) Theorem.
-/

public section

open Polynomial IntermediateField

namespace TauCeti

namespace AlgebraicBelyiPair

universe u

variable {k : Type u} [Field k] [CharZero k]

/-! ### Model from a descended minimal polynomial -/

section ModelOfMinpolyMemLifts

variable (X : AlgebraicBelyiPair k) {K : Type u} [Field K] [CharZero K] [Algebra K k]
  [Algebra (RatFunc K) (RatFunc k)]
  (hC : ∀ c : K, algebraMap (RatFunc K) (RatFunc k) (RatFunc.C c) =
    RatFunc.C (algebraMap K k c))
  (hX : algebraMap (RatFunc K) (RatFunc k) RatFunc.X = RatFunc.X)
  {z : X} (hgen : (RatFunc k)⟮z⟯ = ⊤)
  (hlift : minpoly (RatFunc k) z ∈ Polynomial.lifts (algebraMap (RatFunc K) (RatFunc k)))

/-- **Model from a descended minimal polynomial.** Suppose `z` generates the function field of an
algebraic Belyi pair `X` over `k(t)` and its minimal polynomial over `k(t)` lifts to `K(t)` along a
`K`-compatible map `K(t) → k(t)` sending `t` to `t`. Then the subfield `K(t)(z)` of `X` is an
algebraic Belyi pair over `K` and a model of `X` over `K`, with no algebraicity assumption on
`k / K`. -/
noncomputable def modelOfMinpolyMemLifts : Model K X :=
  letI : Algebra K X := ((algebraMap k X).comp (algebraMap K k)).toAlgebra
  haveI : IsScalarTower K k X := .of_algebraMap_eq fun _ ↦ rfl
  letI : Algebra (RatFunc K) X :=
    ((algebraMap (RatFunc k) X).comp (algebraMap (RatFunc K) (RatFunc k))).toAlgebra
  haveI : IsScalarTower (RatFunc K) (RatFunc k) X := .of_algebraMap_eq fun _ ↦ rfl
  haveI := RatFunc.isScalarTower_of_algebraMap_C hC
  haveI : IsScalarTower K (RatFunc K) X := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply K k X, IsScalarTower.algebraMap_apply k (RatFunc k) X,
      ← IsScalarTower.algebraMap_apply K k (RatFunc k),
      IsScalarTower.algebraMap_apply K (RatFunc K) (RatFunc k),
      ← IsScalarTower.algebraMap_apply (RatFunc K) (RatFunc k) X]
  let E : IntermediateField (RatFunc K) X := (RatFunc K)⟮z⟯
  have hz : IsIntegral (RatFunc k) z := Algebra.IsIntegral.isIntegral z
  have hzK : IsIntegral (RatFunc K) z := hz.of_minpoly_mem_lifts hlift
  haveI : FiniteDimensional (RatFunc K) E := IntermediateField.adjoin.finiteDimensional hzK
  have hex : IsIntegrallyClosedIn K E :=
    isIntegrallyClosedIn_adjoin_simple_ratFunc_of_minpoly_mem_lifts
      X.isAlgebraicBelyiPair.isIntegrallyClosedIn hlift
  have hcomp : constantCompositum E k X = ⊤ :=
    constantCompositum_adjoin_simple_ratFunc_eq_top hX hgen
  have hXE : algebraMap E X (algebraMap (RatFunc K) E RatFunc.X) =
      algebraMap (RatFunc k) X RatFunc.X := by
    rw [← IsScalarTower.algebraMap_apply (RatFunc K) E X,
      IsScalarTower.algebraMap_apply (RatFunc K) (RatFunc k) X, hX]
  { pair :=
      { carrier := E
        isAlgebraicBelyiPair :=
          (isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top hex hcomp hXE).mp
            X.isAlgebraicBelyiPair }
    embedding := algebraMap E X
    embedding_algebraMap := fun c ↦ by
      rw [← IsScalarTower.algebraMap_apply K E X]
      rfl
    embedding_algebraMap_X := hXE
    adjoin_range_embedding := by
      rw [← IntermediateField.toSubfield_inj, IntermediateField.top_toSubfield,
        constantCompositum_def, IntermediateField.adjoin_toSubfield] at hcomp
      rw [← IntermediateField.toSubfield_inj, IntermediateField.top_toSubfield,
        IntermediateField.adjoin_toSubfield, Set.union_comm, hcomp] }

/-- The distinguished generator of `(X.modelOfMinpolyMemLifts hC hX hgen hlift).pair` over `K(t)`,
whose image under the model embedding is `z`
(`TauCeti.AlgebraicBelyiPair.embedding_modelOfMinpolyMemLiftsGen`). -/
noncomputable def modelOfMinpolyMemLiftsGen :
    (X.modelOfMinpolyMemLifts hC hX hgen hlift).pair :=
  letI : Algebra (RatFunc K) X :=
    ((algebraMap (RatFunc k) X).comp (algebraMap (RatFunc K) (RatFunc k))).toAlgebra
  IntermediateField.AdjoinSimple.gen (RatFunc K) z

/-- The embedding of `modelOfMinpolyMemLifts` sends its distinguished generator to `z`. -/
@[simp]
theorem embedding_modelOfMinpolyMemLiftsGen :
    (X.modelOfMinpolyMemLifts hC hX hgen hlift).embedding
      (X.modelOfMinpolyMemLiftsGen hC hX hgen hlift) = z :=
  (rfl)

/-- On `K(t)`, the embedding of `modelOfMinpolyMemLifts` agrees with `K(t) → k(t) → X`. -/
@[simp]
theorem embedding_modelOfMinpolyMemLifts_algebraMap_ratFunc (r : RatFunc K) :
    (X.modelOfMinpolyMemLifts hC hX hgen hlift).embedding
      (algebraMap (RatFunc K) (X.modelOfMinpolyMemLifts hC hX hgen hlift).pair r) =
      algebraMap (RatFunc k) X (algebraMap (RatFunc K) (RatFunc k) r) :=
  (rfl)

/-- The distinguished generator generates the function field of `modelOfMinpolyMemLifts` over
`K(t)`. -/
theorem adjoin_modelOfMinpolyMemLiftsGen :
    (RatFunc K)⟮X.modelOfMinpolyMemLiftsGen hC hX hgen hlift⟯ = ⊤ := by
  let _ : Algebra (RatFunc K) X :=
    ((algebraMap (RatFunc k) X).comp (algebraMap (RatFunc K) (RatFunc k))).toAlgebra
  exact IntermediateField.adjoin_adjoinSimple_gen_eq_top (F := RatFunc K) z

/-- The minimal polynomial over `K(t)` of the distinguished generator of `modelOfMinpolyMemLifts`
maps along `K(t) → k(t)` to `minpoly (RatFunc k) z`. -/
theorem map_minpoly_modelOfMinpolyMemLiftsGen :
    (minpoly (RatFunc K) (X.modelOfMinpolyMemLiftsGen hC hX hgen hlift)).map
      (algebraMap (RatFunc K) (RatFunc k)) = minpoly (RatFunc k) z := by
  let _ : Algebra (RatFunc K) X :=
    ((algebraMap (RatFunc k) X).comp (algebraMap (RatFunc K) (RatFunc k))).toAlgebra
  have : IsScalarTower (RatFunc K) (RatFunc k) X := .of_algebraMap_eq fun _ ↦ rfl
  have hz : IsIntegral (RatFunc k) z := Algebra.IsIntegral.isIntegral z
  have hzK : IsIntegral (RatFunc K) z := hz.of_minpoly_mem_lifts hlift
  have hmp : minpoly (RatFunc K) (X.modelOfMinpolyMemLiftsGen hC hX hgen hlift) =
      minpoly (RatFunc K) z :=
    IntermediateField.minpoly_gen (RatFunc K) z
  rw [hmp]
  exact minpoly.map_algebraMap hzK hlift

/-- Given a compatible `K(t)`-algebra structure on `X`, the function field of
`modelOfMinpolyMemLifts` is canonically isomorphic over `K(t)` to the subfield `K(t)(z)` of `X`. -/
noncomputable def modelOfMinpolyMemLiftsEquiv [Algebra (RatFunc K) X]
    [IsScalarTower (RatFunc K) (RatFunc k) X] :
    (X.modelOfMinpolyMemLifts hC hX hgen hlift).pair ≃ₐ[RatFunc K] (RatFunc K)⟮z⟯ :=
  let f : (X.modelOfMinpolyMemLifts hC hX hgen hlift).pair →ₐ[RatFunc K] X :=
    { (X.modelOfMinpolyMemLifts hC hX hgen hlift).embedding with
      commutes' := fun r ↦ by
        rw [RingHom.toFun_eq_coe,
          X.embedding_modelOfMinpolyMemLifts_algebraMap_ratFunc hC hX hgen hlift r,
          ← IsScalarTower.algebraMap_apply (RatFunc K) (RatFunc k) X] }
  have hrange : f.fieldRange = (RatFunc K)⟮z⟯ := by
    rw [AlgHom.fieldRange_eq_map, ← X.adjoin_modelOfMinpolyMemLiftsGen hC hX hgen hlift,
      IntermediateField.adjoin_map, Set.image_singleton]
    exact congrArg (fun a ↦ (RatFunc K)⟮a⟯)
      (X.embedding_modelOfMinpolyMemLiftsGen hC hX hgen hlift)
  let f' : (X.modelOfMinpolyMemLifts hC hX hgen hlift).pair →ₐ[RatFunc K] (RatFunc K)⟮z⟯ :=
    { toFun := fun y ↦ ⟨f y, by
        have hy : f y ∈ f.fieldRange := AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩
        rwa [hrange] at hy⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun a b ↦ Subtype.ext (f.map_mul a b)
      map_zero' := Subtype.ext f.map_zero
      map_add' := fun a b ↦ Subtype.ext (f.map_add a b)
      commutes' := fun r ↦ Subtype.ext (f.commutes r) }
  AlgEquiv.ofBijective f'
    ⟨fun _ _ h ↦ f.toRingHom.injective (congrArg (fun u : (RatFunc K)⟮z⟯ ↦ (u : X)) h),
      fun ⟨w, hw⟩ ↦ by
        rw [← hrange] at hw
        obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hw
        exact ⟨y, rfl⟩⟩

/-- Under `modelOfMinpolyMemLiftsEquiv`, coercing to `X` recovers the model embedding. -/
@[simp]
theorem coe_modelOfMinpolyMemLiftsEquiv [Algebra (RatFunc K) X]
    [IsScalarTower (RatFunc K) (RatFunc k) X]
    (y : (X.modelOfMinpolyMemLifts hC hX hgen hlift).pair) :
    ((X.modelOfMinpolyMemLiftsEquiv hC hX hgen hlift y : (RatFunc K)⟮z⟯) : X) =
      (X.modelOfMinpolyMemLifts hC hX hgen hlift).embedding y :=
  (rfl)

/-- `modelOfMinpolyMemLiftsEquiv` carries the distinguished generator to `AdjoinSimple.gen`. -/
@[simp]
theorem modelOfMinpolyMemLiftsEquiv_modelOfMinpolyMemLiftsGen [Algebra (RatFunc K) X]
    [IsScalarTower (RatFunc K) (RatFunc k) X] :
    X.modelOfMinpolyMemLiftsEquiv hC hX hgen hlift
      (X.modelOfMinpolyMemLiftsGen hC hX hgen hlift) =
      IntermediateField.AdjoinSimple.gen (RatFunc K) z :=
  Subtype.ext (X.embedding_modelOfMinpolyMemLiftsGen hC hX hgen hlift)

/-- The inverse of `modelOfMinpolyMemLiftsEquiv` sends `AdjoinSimple.gen` back to the
distinguished generator. -/
@[simp]
theorem modelOfMinpolyMemLiftsEquiv_symm_gen [Algebra (RatFunc K) X]
    [IsScalarTower (RatFunc K) (RatFunc k) X] :
    (X.modelOfMinpolyMemLiftsEquiv hC hX hgen hlift).symm
      (IntermediateField.AdjoinSimple.gen (RatFunc K) z) =
      X.modelOfMinpolyMemLiftsGen hC hX hgen hlift := by
  rw [AlgEquiv.symm_apply_eq, modelOfMinpolyMemLiftsEquiv_modelOfMinpolyMemLiftsGen]

/-- The image of the embedding of `modelOfMinpolyMemLifts` in `X` is the subfield `K(t)(z)`. -/
theorem range_embedding_modelOfMinpolyMemLifts [Algebra (RatFunc K) X]
    [IsScalarTower (RatFunc K) (RatFunc k) X] :
    Set.range (X.modelOfMinpolyMemLifts hC hX hgen hlift).embedding = ((RatFunc K)⟮z⟯ : Set X) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [← X.coe_modelOfMinpolyMemLiftsEquiv hC hX hgen hlift y]
    exact (X.modelOfMinpolyMemLiftsEquiv hC hX hgen hlift y).property
  · intro hx
    refine ⟨(X.modelOfMinpolyMemLiftsEquiv hC hX hgen hlift).symm ⟨x, hx⟩, ?_⟩
    rw [← X.coe_modelOfMinpolyMemLiftsEquiv hC hX hgen hlift, AlgEquiv.apply_symm_apply]

end ModelOfMinpolyMemLifts

/-! ### Descent to the pointed field of moduli -/

section Pointed

variable (X : AlgebraicBelyiPair k)

/-- **Pointed model over the pointed field of moduli.** At a rational unbranched place `P` of degree
one over `t = q` (`q ∈ ℚ \ {0, 1}`), the Laurent-normalized generator of `X` over `k(t)` cuts out a
model of `X` over `X.pointedFieldOfModuli P`. No algebraicity of `k` over `ℚ` is assumed. -/
noncomputable def pointedModel {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) :
    Model (X.pointedFieldOfModuli P) X :=
  let K := X.pointedFieldOfModuli P
  letI : Algebra (RatFunc K) (RatFunc k) := (ratFuncMapRingHom K k).toAlgebra
  have hC (c : K) : algebraMap (RatFunc K) (RatFunc k) (RatFunc.C c) = RatFunc.C (c : k) :=
    ratFuncMapRingHom_C K k c
  have hX : algebraMap (RatFunc K) (RatFunc k) RatFunc.X = RatFunc.X :=
    ratFuncMapRingHom_X K k
  let h := exists_generator_minpoly_mem_lifts hq₀ hq₁ hPa hP hC hX
  X.modelOfMinpolyMemLifts hC hX h.choose_spec.left h.choose_spec.right

/-- The isomorphism class of `X` is defined over `X.pointedFieldOfModuli P` at any rational
unbranched place `P` of degree one. -/
theorem isDefinedOver_pointedFieldOfModuli {P : Place k X} {q : ℚ}
    (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
    (hP : P.degree = 1) :
    (IsoClass.mk X).IsDefinedOver (X.pointedFieldOfModuli P) :=
  IsoClass.isDefinedOver_mk_iff.mpr ⟨X.pointedModel hq₀ hq₁ hPa hP⟩

/-- Choosing a rational place over `t = 2` when `k` is algebraically closed. -/
private theorem exists_place_over_two [IsAlgClosed k] :
    ∃ P : Place k X,
      P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C ((2 : ℚ) : k)) ∧
      P.degree = 1 := by
  have hF : IsFunctionField k X := (IsFunctionField.ratFunc k).finite_extension
  obtain ⟨P, hPa⟩ := Place.restrict_surjective (k := k) (F := RatFunc k) (k' := k) (F' := X) hF
    (Place.adicOfIrreducible (irreducible_X_sub_C ((2 : ℚ) : k)))
  exact ⟨P, hPa, P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF⟩

/-- **Köck, Theorem 2.2 (bounded-degree descent over the field of moduli).** Over any algebraically
closed field `k` of characteristic zero (such as `ℂ` or `AlgebraicClosure ℚ`), every algebraic Belyi
pair `X` admits a model over a finite extension `K` of its field of moduli of relative degree at
most `[X : k(t)]`. -/
theorem exists_model_relfinrank_le [IsAlgClosed k] :
    ∃ K : IntermediateField ℚ k,
      (IsoClass.mk X).fieldOfModuli ≤ K ∧
      0 < (IsoClass.mk X).fieldOfModuli.relfinrank K ∧
      (IsoClass.mk X).fieldOfModuli.relfinrank K ≤ Module.finrank (RatFunc k) X ∧
      Nonempty (Model K X) := by
  obtain ⟨P, hPa, hP⟩ := X.exists_place_over_two
  have h20 : ((2 : ℚ) : k) ≠ 0 := by norm_num
  have h21 : ((2 : ℚ) : k) ≠ 1 := by norm_num
  exact ⟨X.pointedFieldOfModuli P, X.fieldOfModuli_le_pointedFieldOfModuli P,
    X.relfinrank_pointedFieldOfModuli_pos hPa, X.relfinrank_pointedFieldOfModuli_le hPa,
    ⟨X.pointedModel h20 h21 hPa hP⟩⟩

/-- If the field of moduli of `X` is finite over `ℚ`, then `X` has a model over a number field `K`
inside `k` containing its field of moduli with `[K : ℚ] ≤ [M(X) : ℚ] · [X : k(t)]`. -/
theorem exists_model_of_finiteDimensional_fieldOfModuli [IsAlgClosed k]
    [FiniteDimensional ℚ (IsoClass.mk X).fieldOfModuli] :
    ∃ K : IntermediateField ℚ k,
      (IsoClass.mk X).fieldOfModuli ≤ K ∧
      FiniteDimensional ℚ K ∧
      Module.finrank ℚ K ≤
        Module.finrank ℚ (IsoClass.mk X).fieldOfModuli * Module.finrank (RatFunc k) X ∧
      Nonempty (Model K X) := by
  obtain ⟨K, hle, hpos, hdeg, hM⟩ := X.exists_model_relfinrank_le
  have hmul := (IntermediateField.finrank_bot_mul_relfinrank hle).symm
  have hKpos : 0 < Module.finrank ℚ K := by
    rw [hmul]
    exact Nat.mul_pos Module.finrank_pos hpos
  exact ⟨K, hle, Module.finite_of_finrank_pos hKpos,
    hmul ▸ Nat.mul_le_mul_left _ hdeg, hM⟩

end Pointed

namespace IsoClass

/-- **Köck, Theorem 2.2 (isomorphism-class form).** Over an algebraically closed field `k` of
characteristic zero, every isomorphism class `c` of algebraic Belyi pairs is defined over a finite
extension `K` of `c.fieldOfModuli` of relative degree at most `c.degree`. -/
theorem exists_isDefinedOver_relfinrank_le [IsAlgClosed k] (c : IsoClass k) :
    ∃ K : IntermediateField ℚ k,
      c.fieldOfModuli ≤ K ∧
      0 < c.fieldOfModuli.relfinrank K ∧
      c.fieldOfModuli.relfinrank K ≤ c.degree ∧
      c.IsDefinedOver K := by
  obtain ⟨X, rfl⟩ := mk_surjective c
  obtain ⟨K, hle, hpos, hdeg, hM⟩ := X.exists_model_relfinrank_le
  exact ⟨K, hle, hpos, by simpa only [degree_mk] using hdeg, isDefinedOver_mk_iff.mpr hM⟩

/-- Over an algebraically closed field `k` of characteristic zero, any isomorphism class `c` whose
field of moduli is finite over `ℚ` is defined over a number field `K ⊆ k` containing
`c.fieldOfModuli` of degree `[K : ℚ] ≤ [c.fieldOfModuli : ℚ] · c.degree`. -/
theorem exists_isDefinedOver_of_finiteDimensional_fieldOfModuli [IsAlgClosed k]
    (c : IsoClass k) [FiniteDimensional ℚ c.fieldOfModuli] :
    ∃ K : IntermediateField ℚ k,
      c.fieldOfModuli ≤ K ∧
      FiniteDimensional ℚ K ∧
      Module.finrank ℚ K ≤ Module.finrank ℚ c.fieldOfModuli * c.degree ∧
      c.IsDefinedOver K := by
  obtain ⟨X, rfl⟩ := mk_surjective c
  obtain ⟨K, hle, hfin, hdeg, hM⟩ := X.exists_model_of_finiteDimensional_fieldOfModuli
  exact ⟨K, hle, hfin, by simpa only [degree_mk] using hdeg, isDefinedOver_mk_iff.mpr hM⟩

end IsoClass

/-! ### Galois Belyi pairs descend to their field of moduli -/

section Galois

variable (X : AlgebraicBelyiPair k)

/-- For a Galois Belyi pair `X / k(t)`, the pointed stabilizer at any place `P` over a rational
point `t = q` (`q ∈ ℚ`) equals the full stabilizer of the isomorphism class of `X`: any semilinear
automorphism moves `P` to another place over `t = q`, and `Gal(X / k(t))` acts transitively on that
fibre. -/
theorem pointedStabilizer_eq_stabilizer_of_isGalois [IsGalois (RatFunc k) X]
    {P : Place k X} {q : ℚ}
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k))) :
    X.pointedStabilizer P = MulAction.stabilizer (k ≃ₐ[ℚ] k) (IsoClass.mk X) := by
  refine le_antisymm (X.pointedStabilizer_le_stabilizer P) fun g hg ↦ ?_
  rw [← X.map_snd_semilinearAut] at hg
  obtain ⟨p, hp, hpg⟩ := hg
  rw [MonoidHom.coe_snd] at hpg
  subst hpg
  let p₀ : semilinearAut X := ⟨p, hp⟩
  have hres : (p₀ • P).restrict k (RatFunc k) = P.restrict k (RatFunc k) := by
    rw [restrict_smul, hPa, Place.equivOfRingEquiv_mapRingEquiv_adicOfIrreducible_X_sub_C,
      map_ratCast]
  obtain ⟨σ, hσ⟩ := Place.exists_smul_eq_of_restrict_eq hres
  refine mem_pointedStabilizer_iff.mpr ⟨p.fst.trans σ.toRingEquiv, fun r ↦ ?_, fun z ↦ ?_⟩
  · rw [RingEquiv.trans_apply, mem_semilinearAut_iff.mp hp, AlgEquiv.coe_toRingEquiv, σ.commutes]
  · rw [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, ← hσ, Place.valuation_smul_apply,
      valuation_smul_apply p₀ P z, hσ]

/-- For a Galois Belyi pair `X / k(t)`, the pointed field of moduli at any place over `t = q`
(`q ∈ ℚ`) coincides with the field of moduli of `X`. -/
theorem pointedFieldOfModuli_eq_fieldOfModuli_of_isGalois [IsGalois (RatFunc k) X]
    {P : Place k X} {q : ℚ}
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k))) :
    X.pointedFieldOfModuli P = (IsoClass.mk X).fieldOfModuli := by
  rw [pointedFieldOfModuli_def, IsoClass.fieldOfModuli_def,
    X.pointedStabilizer_eq_stabilizer_of_isGalois hPa]

/-- **Köck, Theorem 2.2 (Galois model).** Over any algebraically closed field `k` of characteristic
zero, every Galois Belyi pair `X` admits a model over its field of moduli. -/
noncomputable def modelOfIsGalois [IsAlgClosed k] [IsGalois (RatFunc k) X] :
    Model (IsoClass.mk X).fieldOfModuli X :=
  let h := X.exists_place_over_two
  have h20 : ((2 : ℚ) : k) ≠ 0 := by norm_num
  have h21 : ((2 : ℚ) : k) ≠ 1 := by norm_num
  Eq.rec (motive := fun (L : IntermediateField ℚ k) _ ↦ Model L X)
    (X.pointedModel h20 h21 h.choose_spec.left h.choose_spec.right)
    (X.pointedFieldOfModuli_eq_fieldOfModuli_of_isGalois h.choose_spec.left)

end Galois

namespace IsoClass

/-- **Köck, Theorem 2.2 (Galois case).** Over any algebraically closed field `k` of characteristic
zero (such as `ℂ` or `AlgebraicClosure ℚ`), every Galois Belyi pair is defined over its field of
moduli. -/
theorem isDefinedOver_fieldOfModuli_of_isGalois [IsAlgClosed k] (X : AlgebraicBelyiPair k)
    [IsGalois (RatFunc k) X] :
    (mk X).IsDefinedOver (mk X).fieldOfModuli :=
  isDefinedOver_mk_iff.mpr ⟨X.modelOfIsGalois⟩

end IsoClass

end AlgebraicBelyiPair

end TauCeti
