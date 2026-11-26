/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Model
public import TauCeti.FieldTheory.Minpoly.Lifts
import TauCeti.FieldTheory.FunctionField.Belyi.BaseChange
import TauCeti.FieldTheory.FunctionField.ConstantExtension.MinpolyDescent
import TauCeti.FieldTheory.FunctionField.ConstantExtension.RatFunc

/-!
# Models of algebraic Belyi pairs from descended minimal polynomials

Let `X = (F, k(t) ↪ F)` be an algebraic Belyi pair over a field `k` of characteristic zero, and let
`K → k` be any field extension (algebraic or transcendental) equipped with a `K`-compatible map
`K(t) → k(t)` sending `t` to `t`. Whenever `z ∈ F` generates `F` over `k(t)` and its minimal
polynomial over `k(t)` lifts to `K(t)`, minimal-polynomial descent of exact constants
(`TauCeti.isIntegrallyClosedIn_adjoin_simple_ratFunc_of_minpoly_mem_lifts`) and the arbitrary
constant-extension comparison for Belyi pairs
(`TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`) package `AdjoinRoot` of the
descended minimal polynomial into a universe-polymorphic `TauCeti.AlgebraicBelyiPair.Model` of `X`
over `K` (`TauCeti.AlgebraicBelyiPair.modelOfMinpolyMemLifts`), with carrier in the universe of `K`
and a characteristic API identifying it with the subfield `K(t)(z)` of `F`.

## Main definitions

* `TauCeti.AlgebraicBelyiPair.modelOfMinpolyMemLifts`: the model of `X` over `K` attached to a
  generator `z` of `X / k(t)` whose minimal polynomial lifts to `K(t)`.
* `TauCeti.AlgebraicBelyiPair.modelOfMinpolyMemLiftsGen`: the distinguished generator of
  `modelOfMinpolyMemLifts` corresponding to `z`.
* `TauCeti.AlgebraicBelyiPair.modelOfMinpolyMemLiftsEquiv`: canonical `K(t)`-algebra isomorphism
  identifying the function field of `modelOfMinpolyMemLifts` with the subfield `K(t)(z)` of `X`.

## Main results

* `TauCeti.AlgebraicBelyiPair.embedding_modelOfMinpolyMemLifts_algebraMap_ratFunc`,
  `TauCeti.AlgebraicBelyiPair.embedding_modelOfMinpolyMemLiftsGen`,
  `TauCeti.AlgebraicBelyiPair.adjoin_modelOfMinpolyMemLiftsGen`,
  `TauCeti.AlgebraicBelyiPair.map_minpoly_modelOfMinpolyMemLiftsGen`,
  `TauCeti.AlgebraicBelyiPair.coe_modelOfMinpolyMemLiftsEquiv`,
  `TauCeti.AlgebraicBelyiPair.modelOfMinpolyMemLiftsEquiv_modelOfMinpolyMemLiftsGen`,
  `TauCeti.AlgebraicBelyiPair.modelOfMinpolyMemLiftsEquiv_symm_gen`, and
  `TauCeti.AlgebraicBelyiPair.range_embedding_modelOfMinpolyMemLifts`: characteristic API for
  `modelOfMinpolyMemLifts` without unfolding its definition.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  (2.2) Theorem and its proof.
-/

public section

open Polynomial IntermediateField

namespace TauCeti.AlgebraicBelyiPair

universe u v

variable {k : Type u} [Field k] [CharZero k] (X : AlgebraicBelyiPair k)
  {K : Type v} [Field K] [Algebra (RatFunc K) (RatFunc k)]

/-- Composite `K(t)`-algebra structure on `X` along `K(t) → k(t) → X`. -/
private noncomputable abbrev ratFuncKAlgebra : Algebra (RatFunc K) X :=
  ((algebraMap (RatFunc k) X).comp (algebraMap (RatFunc K) (RatFunc k))).toAlgebra

private theorem ratFuncKAlgebra_algebraMap (r : RatFunc K) :
    letI := X.ratFuncKAlgebra (K := K)
    algebraMap (RatFunc K) X r = algebraMap (RatFunc k) X (algebraMap (RatFunc K) (RatFunc k) r) :=
  letI := X.ratFuncKAlgebra (K := K)
  RingHom.congr_fun (RingHom.algebraMap_toAlgebra _) r

private theorem isScalarTower_ratFuncK :
    letI := X.ratFuncKAlgebra (K := K)
    IsScalarTower (RatFunc K) (RatFunc k) X :=
  letI := X.ratFuncKAlgebra (K := K)
  .of_algebraMap_eq fun r ↦ (X.ratFuncKAlgebra_algebraMap r).symm

private theorem isIntegral_ratFunc_of_minpoly_mem_lifts {z : X}
    (hlift : minpoly (RatFunc k) z ∈ Polynomial.lifts (algebraMap (RatFunc K) (RatFunc k))) :
    letI := X.ratFuncKAlgebra (K := K)
    IsIntegral (RatFunc K) z :=
  letI := X.ratFuncKAlgebra (K := K)
  haveI := X.isScalarTower_ratFuncK (K := K)
  (Algebra.IsIntegral.isIntegral (R := RatFunc k) z).of_minpoly_mem_lifts hlift

/-- Canonical `K(t)`-algebra embedding of `AdjoinRoot (minpoly K(t) z)` into `X` sending the root
to `z`. -/
private noncomputable abbrev minpolyRootHom {z : X}
    (hlift : minpoly (RatFunc k) z ∈ Polynomial.lifts (algebraMap (RatFunc K) (RatFunc k))) :
    letI := X.ratFuncKAlgebra (K := K)
    AdjoinRoot (minpoly (RatFunc K) z) →ₐ[RatFunc K] X :=
  letI := X.ratFuncKAlgebra (K := K)
  have hzK := X.isIntegral_ratFunc_of_minpoly_mem_lifts hlift
  haveI : Fact (Irreducible (minpoly (RatFunc K) z)) := ⟨minpoly.irreducible hzK⟩
  ((RatFunc K)⟮z⟯).val.comp (IntermediateField.adjoinRootEquivAdjoin (RatFunc K) hzK).toAlgHom

private theorem minpolyRootHom_apply {z : X}
    (hlift : minpoly (RatFunc k) z ∈ Polynomial.lifts (algebraMap (RatFunc K) (RatFunc k))) :
    letI := X.ratFuncKAlgebra (K := K)
    ∀ y : AdjoinRoot (minpoly (RatFunc K) z),
      X.minpolyRootHom hlift y =
        ((IntermediateField.adjoinRootEquivAdjoin (RatFunc K)
          (X.isIntegral_ratFunc_of_minpoly_mem_lifts hlift) y : (RatFunc K)⟮z⟯) : X) :=
  -- `minpolyRootHom` is definitionally `((RatFunc K)⟮z⟯).val.comp (adjoinRootEquivAdjoin ..)`.
  fun _ ↦ rfl

private theorem minpolyRootHom_root {z : X}
    (hlift : minpoly (RatFunc k) z ∈ Polynomial.lifts (algebraMap (RatFunc K) (RatFunc k))) :
    letI := X.ratFuncKAlgebra (K := K)
    X.minpolyRootHom hlift (AdjoinRoot.root (minpoly (RatFunc K) z)) = z := by
  let _ := X.ratFuncKAlgebra (K := K)
  rw [X.minpolyRootHom_apply hlift, IntermediateField.adjoinRootEquivAdjoin_apply_root,
    IntermediateField.AdjoinSimple.coe_gen]

private theorem range_minpolyRootHom {z : X}
    (hlift : minpoly (RatFunc k) z ∈ Polynomial.lifts (algebraMap (RatFunc K) (RatFunc k))) :
    letI := X.ratFuncKAlgebra (K := K)
    Set.range (X.minpolyRootHom hlift).toRingHom = Set.range (algebraMap (RatFunc K)⟮z⟯ X) := by
  let _ := X.ratFuncKAlgebra (K := K)
  let hzK := X.isIntegral_ratFunc_of_minpoly_mem_lifts hlift
  have : Fact (Irreducible (minpoly (RatFunc K) z)) := ⟨minpoly.irreducible hzK⟩
  have hcoe : ((X.minpolyRootHom hlift).toRingHom : _ → X) =
      Subtype.val ∘ IntermediateField.adjoinRootEquivAdjoin (RatFunc K) hzK :=
    funext (X.minpolyRootHom_apply hlift)
  rw [hcoe, (IntermediateField.adjoinRootEquivAdjoin (RatFunc K) hzK).surjective.range_comp,
    Subtype.range_coe]
  exact Subtype.range_coe.symm

private theorem minpolyRootHom_algebraMap_X
    (hX : algebraMap (RatFunc K) (RatFunc k) RatFunc.X = RatFunc.X) {z : X}
    (hlift : minpoly (RatFunc k) z ∈ Polynomial.lifts (algebraMap (RatFunc K) (RatFunc k))) :
    letI := X.ratFuncKAlgebra (K := K)
    haveI : Fact (Irreducible (minpoly (RatFunc K) z)) :=
      ⟨minpoly.irreducible (X.isIntegral_ratFunc_of_minpoly_mem_lifts hlift)⟩
    (X.minpolyRootHom hlift).toRingHom
      (algebraMap (RatFunc K) (AdjoinRoot (minpoly (RatFunc K) z)) RatFunc.X) =
      algebraMap (RatFunc k) X RatFunc.X := by
  let _ := X.ratFuncKAlgebra (K := K)
  have : Fact (Irreducible (minpoly (RatFunc K) z)) :=
    ⟨minpoly.irreducible (X.isIntegral_ratFunc_of_minpoly_mem_lifts hlift)⟩
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, (X.minpolyRootHom hlift).commutes,
    X.ratFuncKAlgebra_algebraMap, hX]

section ModelOfMinpolyMemLifts

variable [Algebra K k]
  (hC : ∀ c : K, algebraMap (RatFunc K) (RatFunc k) (RatFunc.C c) =
    RatFunc.C (algebraMap K k c))
  (hX : algebraMap (RatFunc K) (RatFunc k) RatFunc.X = RatFunc.X)
  {z : X} (hgen : (RatFunc k)⟮z⟯ = ⊤)
  (hlift : minpoly (RatFunc k) z ∈ Polynomial.lifts (algebraMap (RatFunc K) (RatFunc k)))

private noncomputable abbrev baseKAlgebra : Algebra K X :=
  ((algebraMap k X).comp (algebraMap K k)).toAlgebra

include hC in
private theorem isScalarTowers_baseK :
    letI := X.baseKAlgebra (K := K)
    letI := X.ratFuncKAlgebra (K := K)
    IsScalarTower K k X ∧ IsScalarTower K (RatFunc K) X := by
  let _ := X.baseKAlgebra (K := K)
  let _ := X.ratFuncKAlgebra (K := K)
  have hKk : IsScalarTower K k X :=
    .of_algebraMap_eq fun c ↦ (RingHom.congr_fun (RingHom.algebraMap_toAlgebra _) c).symm
  refine ⟨hKk, .of_algebraMap_eq fun c ↦ ?_⟩
  rw [IsScalarTower.algebraMap_apply K k X, X.ratFuncKAlgebra_algebraMap,
    RatFunc.algebraMap_eq_C, hC, ← RatFunc.algebraMap_eq_C,
    ← IsScalarTower.algebraMap_apply k (RatFunc k) X]

include hC in
private theorem minpolyRootHom_algebraMap (c : K) :
    letI := X.ratFuncKAlgebra (K := K)
    haveI : Fact (Irreducible (minpoly (RatFunc K) z)) :=
      ⟨minpoly.irreducible (X.isIntegral_ratFunc_of_minpoly_mem_lifts hlift)⟩
    (X.minpolyRootHom hlift).toRingHom (algebraMap K (AdjoinRoot (minpoly (RatFunc K) z)) c) =
      algebraMap k X (algebraMap K k c) := by
  let _ := X.ratFuncKAlgebra (K := K)
  have : Fact (Irreducible (minpoly (RatFunc K) z)) :=
    ⟨minpoly.irreducible (X.isIntegral_ratFunc_of_minpoly_mem_lifts hlift)⟩
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    IsScalarTower.algebraMap_apply K (RatFunc K) (AdjoinRoot (minpoly (RatFunc K) z)),
    (X.minpolyRootHom hlift).commutes, X.ratFuncKAlgebra_algebraMap, RatFunc.algebraMap_eq_C, hC,
    ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply k (RatFunc k) X]

include hC hX hgen in
private theorem adjoin_range_minpolyRootHom :
    letI := X.ratFuncKAlgebra (K := K)
    IntermediateField.adjoin k (Set.range (X.minpolyRootHom hlift).toRingHom) = ⊤ := by
  let _ := X.baseKAlgebra (K := K)
  let _ := X.ratFuncKAlgebra (K := K)
  have := X.isScalarTower_ratFuncK (K := K)
  have := RatFunc.isScalarTower_of_algebraMap_C hC
  obtain ⟨_, _⟩ := X.isScalarTowers_baseK hC
  rw [X.range_minpolyRootHom hlift]
  simpa only [Set.image_univ] using adjoin_image_eq_top_of_constantCompositum_eq_top
    (IntermediateField.adjoin_univ K (RatFunc K)⟮z⟯)
    (constantCompositum_adjoin_simple_ratFunc_eq_top hX hgen)

include hC hlift in
private theorem isIntegrallyClosedIn_adjoinRoot_minpoly :
    letI := X.ratFuncKAlgebra (K := K)
    haveI : Fact (Irreducible (minpoly (RatFunc K) z)) :=
      ⟨minpoly.irreducible (X.isIntegral_ratFunc_of_minpoly_mem_lifts hlift)⟩
    IsIntegrallyClosedIn K (AdjoinRoot (minpoly (RatFunc K) z)) := by
  let _ := X.baseKAlgebra (K := K)
  let _ := X.ratFuncKAlgebra (K := K)
  have := X.isScalarTower_ratFuncK (K := K)
  obtain ⟨_, _⟩ := X.isScalarTowers_baseK hC
  have hzK := X.isIntegral_ratFunc_of_minpoly_mem_lifts hlift
  have : Fact (Irreducible (minpoly (RatFunc K) z)) := ⟨minpoly.irreducible hzK⟩
  exact ((IntermediateField.adjoinRootEquivAdjoin (RatFunc K) hzK).restrictScalars
    K).isIntegrallyClosedIn.mpr <|
    isIntegrallyClosedIn_adjoin_simple_ratFunc_of_minpoly_mem_lifts
      X.isAlgebraicBelyiPair.isIntegrallyClosedIn hlift

variable [CharZero K]
include hC hX hgen hlift

private theorem isAlgebraicBelyiPair_adjoinRoot_minpoly :
    letI := X.ratFuncKAlgebra (K := K)
    haveI : Fact (Irreducible (minpoly (RatFunc K) z)) :=
      ⟨minpoly.irreducible (X.isIntegral_ratFunc_of_minpoly_mem_lifts hlift)⟩
    haveI : FiniteDimensional (RatFunc K) (AdjoinRoot (minpoly (RatFunc K) z)) :=
      (minpoly.monic (X.isIntegral_ratFunc_of_minpoly_mem_lifts hlift)).finite_adjoinRoot
    IsAlgebraicBelyiPair K (AdjoinRoot (minpoly (RatFunc K) z)) := by
  let _ := X.baseKAlgebra (K := K)
  let _ := X.ratFuncKAlgebra (K := K)
  obtain ⟨_, _⟩ := X.isScalarTowers_baseK hC
  have hzK := X.isIntegral_ratFunc_of_minpoly_mem_lifts hlift
  let F₀ : Type v := AdjoinRoot (minpoly (RatFunc K) z)
  have : Fact (Irreducible (minpoly (RatFunc K) z)) := ⟨minpoly.irreducible hzK⟩
  have : FiniteDimensional (RatFunc K) F₀ := (minpoly.monic hzK).finite_adjoinRoot
  let _ : Algebra F₀ X := (X.minpolyRootHom hlift).toRingHom.toAlgebra
  have : IsScalarTower K F₀ X := .of_algebraMap_eq fun c ↦
    (IsScalarTower.algebraMap_apply K k X c).trans (X.minpolyRootHom_algebraMap hC hlift c).symm
  have hcomp : constantCompositum F₀ k X = ⊤ :=
    constantCompositum_eq_top_of_adjoin_eq_top F₀ k X
      (X.adjoin_range_minpolyRootHom hC hX hgen hlift)
  exact (isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top
    (X.isIntegrallyClosedIn_adjoinRoot_minpoly hC hlift) hcomp
    (X.minpolyRootHom_algebraMap_X hX hlift)).mp X.isAlgebraicBelyiPair

/-- **Model from a descended minimal polynomial.** Suppose `z` generates the function field of an
algebraic Belyi pair `X` over `k(t)` and its minimal polynomial over `k(t)` lifts to `K(t)` along a
`K`-compatible map `K(t) → k(t)` sending `t` to `t`. Then `AdjoinRoot (minpoly K(t) z)`, embedded
into `X` onto the subfield `K(t)(z)`, is an algebraic Belyi pair over `K` and a model of `X` over
`K`, with `K` in an independent universe and no algebraicity assumption on `k / K`. -/
noncomputable def modelOfMinpolyMemLifts : Model K X :=
  letI : Algebra (RatFunc K) X := X.ratFuncKAlgebra (K := K)
  have hzK := X.isIntegral_ratFunc_of_minpoly_mem_lifts hlift
  haveI : Fact (Irreducible (minpoly (RatFunc K) z)) := ⟨minpoly.irreducible hzK⟩
  haveI : FiniteDimensional (RatFunc K) (AdjoinRoot (minpoly (RatFunc K) z)) :=
    (minpoly.monic hzK).finite_adjoinRoot
  { pair := ⟨AdjoinRoot (minpoly (RatFunc K) z),
      X.isAlgebraicBelyiPair_adjoinRoot_minpoly hC hX hgen hlift⟩
    embedding := (X.minpolyRootHom hlift).toRingHom
    embedding_algebraMap := X.minpolyRootHom_algebraMap hC hlift
    embedding_algebraMap_X := X.minpolyRootHom_algebraMap_X hX hlift
    adjoin_range_embedding := X.adjoin_range_minpolyRootHom hC hX hgen hlift }

/-- The distinguished generator of `(X.modelOfMinpolyMemLifts hC hX hgen hlift).pair` over `K(t)`,
whose image under the model embedding is `z`
(`TauCeti.AlgebraicBelyiPair.embedding_modelOfMinpolyMemLiftsGen`). -/
noncomputable def modelOfMinpolyMemLiftsGen :
    (X.modelOfMinpolyMemLifts hC hX hgen hlift).pair :=
  letI : Algebra (RatFunc K) X := X.ratFuncKAlgebra (K := K)
  AdjoinRoot.root (minpoly (RatFunc K) z)

/-- Internal `K(t)`-algebra identification of `AdjoinRoot (minpoly K(t) z)` with the function field
of `modelOfMinpolyMemLifts`: both have carrier `AdjoinRoot (minpoly K(t) z)` with its standard
`K(t)`-algebra structure. -/
private noncomputable def adjoinRootEquivModelPair :
    letI := X.ratFuncKAlgebra (K := K)
    haveI : Fact (Irreducible (minpoly (RatFunc K) z)) :=
      ⟨minpoly.irreducible (X.isIntegral_ratFunc_of_minpoly_mem_lifts hlift)⟩
    AdjoinRoot (minpoly (RatFunc K) z) ≃ₐ[RatFunc K]
      (X.modelOfMinpolyMemLifts hC hX hgen hlift).pair :=
  AlgEquiv.refl

private theorem adjoinRootEquivModelPair_root :
    letI := X.ratFuncKAlgebra (K := K)
    X.adjoinRootEquivModelPair hC hX hgen hlift (AdjoinRoot.root (minpoly (RatFunc K) z)) =
      X.modelOfMinpolyMemLiftsGen hC hX hgen hlift :=
  -- Both sides are `AdjoinRoot.root (minpoly (RatFunc K) z)` under `adjoinRootEquivModelPair`.
  rfl

private theorem embedding_adjoinRootEquivModelPair :
    letI := X.ratFuncKAlgebra (K := K)
    ∀ y : AdjoinRoot (minpoly (RatFunc K) z),
      (X.modelOfMinpolyMemLifts hC hX hgen hlift).embedding
        (X.adjoinRootEquivModelPair hC hX hgen hlift y) = X.minpolyRootHom hlift y :=
  -- `modelOfMinpolyMemLifts.embedding` is definitionally `(X.minpolyRootHom hlift).toRingHom`.
  fun _ ↦ rfl

/-- The embedding of `modelOfMinpolyMemLifts` sends its distinguished generator to `z`. -/
@[simp]
theorem embedding_modelOfMinpolyMemLiftsGen :
    (X.modelOfMinpolyMemLifts hC hX hgen hlift).embedding
      (X.modelOfMinpolyMemLiftsGen hC hX hgen hlift) = z := by
  let _ : Algebra (RatFunc K) X := X.ratFuncKAlgebra (K := K)
  rw [← X.adjoinRootEquivModelPair_root hC hX hgen hlift,
    X.embedding_adjoinRootEquivModelPair hC hX hgen hlift, X.minpolyRootHom_root hlift]

/-- On `K(t)`, the embedding of `modelOfMinpolyMemLifts` agrees with `K(t) → k(t) → X`. -/
@[simp]
theorem embedding_modelOfMinpolyMemLifts_algebraMap_ratFunc (r : RatFunc K) :
    (X.modelOfMinpolyMemLifts hC hX hgen hlift).embedding
      (algebraMap (RatFunc K) (X.modelOfMinpolyMemLifts hC hX hgen hlift).pair r) =
      algebraMap (RatFunc k) X (algebraMap (RatFunc K) (RatFunc k) r) := by
  let _ : Algebra (RatFunc K) X := X.ratFuncKAlgebra (K := K)
  have : Fact (Irreducible (minpoly (RatFunc K) z)) :=
    ⟨minpoly.irreducible (X.isIntegral_ratFunc_of_minpoly_mem_lifts hlift)⟩
  rw [← (X.adjoinRootEquivModelPair hC hX hgen hlift).commutes r,
    X.embedding_adjoinRootEquivModelPair hC hX hgen hlift, (X.minpolyRootHom hlift).commutes,
    X.ratFuncKAlgebra_algebraMap]

/-- The distinguished generator generates the function field of `modelOfMinpolyMemLifts` over
`K(t)`. -/
theorem adjoin_modelOfMinpolyMemLiftsGen :
    (RatFunc K)⟮X.modelOfMinpolyMemLiftsGen hC hX hgen hlift⟯ = ⊤ := by
  let _ : Algebra (RatFunc K) X := X.ratFuncKAlgebra (K := K)
  have : Fact (Irreducible (minpoly (RatFunc K) z)) :=
    ⟨minpoly.irreducible (X.isIntegral_ratFunc_of_minpoly_mem_lifts hlift)⟩
  let e := X.adjoinRootEquivModelPair hC hX hgen hlift
  rw [← X.adjoinRootEquivModelPair_root hC hX hgen hlift, ← Set.image_singleton,
    ← AlgEquiv.coe_toAlgHom, ← IntermediateField.adjoin_map,
    IntermediateField.adjoin_root_eq_top (minpoly (RatFunc K) z), ← AlgHom.fieldRange_eq_map]
  exact eq_top_iff.mpr fun y _ ↦ ⟨e.symm y, e.apply_symm_apply y⟩

/-- The minimal polynomial over `K(t)` of the distinguished generator of `modelOfMinpolyMemLifts`
maps along `K(t) → k(t)` to `minpoly (RatFunc k) z`. -/
theorem map_minpoly_modelOfMinpolyMemLiftsGen :
    (minpoly (RatFunc K) (X.modelOfMinpolyMemLiftsGen hC hX hgen hlift)).map
      (algebraMap (RatFunc K) (RatFunc k)) = minpoly (RatFunc k) z := by
  let _ : Algebra (RatFunc K) X := X.ratFuncKAlgebra (K := K)
  have := X.isScalarTower_ratFuncK (K := K)
  have hzK := X.isIntegral_ratFunc_of_minpoly_mem_lifts hlift
  have : Fact (Irreducible (minpoly (RatFunc K) z)) := ⟨minpoly.irreducible hzK⟩
  rw [← X.adjoinRootEquivModelPair_root hC hX hgen hlift,
    minpoly.algEquiv_eq (X.adjoinRootEquivModelPair hC hX hgen hlift),
    AdjoinRoot.minpoly_root (minpoly.ne_zero hzK), (minpoly.monic hzK).leadingCoeff, inv_one,
    map_one, mul_one]
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
  f.equivFieldRange.trans (IntermediateField.equivOfEq hrange)

/-- Under `modelOfMinpolyMemLiftsEquiv`, coercing to `X` recovers the model embedding. -/
@[simp]
theorem coe_modelOfMinpolyMemLiftsEquiv [Algebra (RatFunc K) X]
    [IsScalarTower (RatFunc K) (RatFunc k) X]
    (y : (X.modelOfMinpolyMemLifts hC hX hgen hlift).pair) :
    ((X.modelOfMinpolyMemLiftsEquiv hC hX hgen hlift y : (RatFunc K)⟮z⟯) : X) =
      (X.modelOfMinpolyMemLifts hC hX hgen hlift).embedding y := by
  simp [modelOfMinpolyMemLiftsEquiv]

/-- `modelOfMinpolyMemLiftsEquiv` carries the distinguished generator to `AdjoinSimple.gen`. -/
@[simp]
theorem modelOfMinpolyMemLiftsEquiv_modelOfMinpolyMemLiftsGen [Algebra (RatFunc K) X]
    [IsScalarTower (RatFunc K) (RatFunc k) X] :
    X.modelOfMinpolyMemLiftsEquiv hC hX hgen hlift
      (X.modelOfMinpolyMemLiftsGen hC hX hgen hlift) =
      IntermediateField.AdjoinSimple.gen (RatFunc K) z :=
  Subtype.ext <| (X.coe_modelOfMinpolyMemLiftsEquiv hC hX hgen hlift _).trans
    (X.embedding_modelOfMinpolyMemLiftsGen hC hX hgen hlift)

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
  have hcoe : ((X.modelOfMinpolyMemLifts hC hX hgen hlift).embedding : _ → X) =
      Subtype.val ∘ X.modelOfMinpolyMemLiftsEquiv hC hX hgen hlift :=
    funext fun y ↦ (X.coe_modelOfMinpolyMemLiftsEquiv hC hX hgen hlift y).symm
  rw [hcoe, (X.modelOfMinpolyMemLiftsEquiv hC hX hgen hlift).surjective.range_comp,
    Subtype.range_coe]

end ModelOfMinpolyMemLifts

end TauCeti.AlgebraicBelyiPair
