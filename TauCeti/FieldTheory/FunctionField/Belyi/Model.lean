/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.FieldOfModuli
public import Mathlib.RingTheory.TensorProduct.Basic
import TauCeti.FieldTheory.AlgebraicClosure
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Regular
import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Models of algebraic Belyi pairs and fields of definition

Let `X = (F, k(t) ↪ F)` be an algebraic Belyi pair over a field `k` of characteristic zero, such
as `AlgebraicClosure ℚ` or `ℂ`, and let `K → k` be a field extension, such as a number field
inside `AlgebraicClosure ℚ` or `ℂ`. A **model** of `X` over `K` is an algebraic Belyi pair
`Y = (F₀, K(t) ↪ F₀)` over `K` together with an embedding `F₀ ↪ F` which is the given map on the
constants, sends `t` to `t`, and whose image generates `F` over `k`. For any extension `k / K`
(algebraic or transcendental), `k ⊗[K] F₀` is a domain whose fraction field is canonically
isomorphic to `F` over `k` (`TauCeti.AlgebraicBelyiPair.Model.fractionRingEquiv`), and the model
has the same degree over `K(t)` as `X` has over `k(t)`
(`TauCeti.AlgebraicBelyiPair.Model.finrank_pair`). When `k / K` is algebraic, multiplication
already identifies `F₀ ⊗[K] k` with `F` (`TauCeti.AlgebraicBelyiPair.Model.baseChangeEquiv`): the
exact constant field `K` of `F₀` makes the tensor product a field, and the generation hypothesis
makes multiplication onto. So a model is an algebraic Belyi pair over `K` with an isomorphism from
its function-field base change to `k` onto `X`. An isomorphism class of pairs over `k` is
**defined over** `K` when one, equivalently every, representative has a model over `K`.

A model makes every automorphism `σ` of `k` over `K` (algebraic or transcendental) act on `F`, as
`σ ⊗ id` lifted to `FractionRing (k ⊗[K] F₀)` (`TauCeti.AlgebraicBelyiPair.Model.baseChangeAut`).
This automorphism fixes the model and `t`, and applies `σ` to the coefficients of `k(t)`, so it is
an isomorphism of pairs from the conjugate `X^σ` to `X`. Hence the automorphisms of `k` fixing `K`
stabilize the class of `X`, and when `k / K` is Galois, the field of moduli of the class is
contained in `K`: **every field of definition contains the field of moduli**. The converse fails in
general: a class need not be defined over its field of moduli (Couveignes).

## Main definitions

* `TauCeti.AlgebraicBelyiPair.Model`: a model of an algebraic Belyi pair over a subfield.
* `TauCeti.AlgebraicBelyiPair.Model.trans`: composition of models along a tower of constant fields.
* `TauCeti.AlgebraicBelyiPair.Model.fractionRingEquiv`: for arbitrary `k / K`, the `k`-algebra
  isomorphism `FractionRing (k ⊗[K] M.pair) ≃ₐ[k] X`.
* `TauCeti.AlgebraicBelyiPair.Model.baseChangeEquiv`: for algebraic `k / K`, the isomorphism
  `F₀ ⊗[K] k ≃+* F`.
* `TauCeti.AlgebraicBelyiPair.Model.baseChangeAut`: for arbitrary `k / K`, the automorphism of the
  pair induced by an automorphism of the constants fixing the field of the model.
* `TauCeti.AlgebraicBelyiPair.IsoClass.IsDefinedOver`: an isomorphism class is defined over a
  subfield.

## Main results

* `TauCeti.AlgebraicBelyiPair.Model.finrank_pair`: a model over any `K → k` has the same degree
  over `K(t)` as `X` has over `k(t)`.
* `TauCeti.AlgebraicBelyiPair.Model.smul_mk_eq_mk`: an automorphism of `k` fixing the field of a
  model fixes the class of the pair.
* `TauCeti.AlgebraicBelyiPair.IsoClass.IsDefinedOver.fieldOfModuli_le`: the field of moduli of a
  class is contained in every field of definition over which `k` is Galois.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  Section 1 and (2.1) Definition.
* J.-M. Couveignes, *Calcul et rationalité de fonctions de Belyi en genre 0*, Annales de
  l'Institut Fourier 44 (1994), 1–38, for Belyi maps not defined over their field of moduli.
-/

public section

universe u v w

open scoped TensorProduct

namespace TauCeti

namespace AlgebraicBelyiPair

variable {k : Type u} [Field k] [CharZero k] {K : Type v} [Field K] [CharZero K] [Algebra K k]

variable (K) in
/-- A **model** of an algebraic Belyi pair `X = (F, k(t) ↪ F)` over a field `K → k`: an algebraic
Belyi pair `Y = (F₀, K(t) ↪ F₀)` over `K` with an embedding `F₀ ↪ F` that is the map `K → k` on
the constants, sends `t` to `t`, and whose image generates `F` over `k`. For arbitrary `k / K` it
identifies `FractionRing (k ⊗[K] F₀)` with `F`
(`TauCeti.AlgebraicBelyiPair.Model.fractionRingEquiv`), and for algebraic `k / K` it identifies
`F₀ ⊗[K] k` with `F` (`TauCeti.AlgebraicBelyiPair.Model.baseChangeEquiv`). -/
structure Model (X : AlgebraicBelyiPair k) where
  /-- The algebraic Belyi pair over `K`. -/
  pair : AlgebraicBelyiPair K
  /-- The embedding of the function field of the model into that of `X`. -/
  embedding : pair →+* X
  embedding_algebraMap (c : K) : embedding (algebraMap K pair c) = algebraMap k X (algebraMap K k c)
  embedding_algebraMap_X :
    embedding (algebraMap (RatFunc K) pair RatFunc.X) = algebraMap (RatFunc k) X RatFunc.X
  adjoin_range_embedding : IntermediateField.adjoin k (Set.range embedding) = ⊤

namespace Model

variable {X X' : AlgebraicBelyiPair k}

attribute [simp] embedding_algebraMap embedding_algebraMap_X

variable (X) in
/-- Every algebraic Belyi pair is a model of itself over its own field of constants. -/
@[expose, simps]
def refl : Model k X where
  pair := X
  embedding := RingHom.id X
  embedding_algebraMap _ := rfl
  embedding_algebraMap_X := rfl
  adjoin_range_embedding := by
    rw [RingHom.coe_id, Set.range_id, IntermediateField.adjoin_univ]

/-- A model of a pair is a model of every isomorphic pair, through the isomorphism. -/
@[expose, simps pair embedding]
noncomputable def mapAlgEquiv (M : Model K X) (e : X ≃ₐ[RatFunc k] X') : Model K X' where
  pair := M.pair
  embedding := (e : X →+* X').comp M.embedding
  embedding_algebraMap c := by
    rw [RingHom.comp_apply, embedding_algebraMap, IsScalarTower.algebraMap_apply k (RatFunc k) X,
      RingHom.coe_coe, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  embedding_algebraMap_X := by
    rw [RingHom.comp_apply, embedding_algebraMap_X, RingHom.coe_coe, AlgEquiv.commutes]
  adjoin_range_embedding := by
    rw [RingHom.coe_comp, Set.range_comp, RingHom.coe_coe,
      ← AlgEquiv.coe_restrictScalars (R := k), ← AlgEquiv.coe_toAlgHom,
      ← IntermediateField.adjoin_map, M.adjoin_range_embedding, ← AlgHom.fieldRange_eq_map]
    exact eq_top_iff.mpr fun x _ ↦ AlgHom.mem_fieldRange.mpr ⟨e.symm x, e.apply_symm_apply x⟩

variable (M : Model K X)

/-- Composition of models along a tower of constant fields `K₀ → K → k`. -/
@[expose, simps pair embedding]
def trans {K₀ : Type w} [Field K₀] [CharZero K₀] [Algebra K₀ K] [Algebra K₀ k]
    [IsScalarTower K₀ K k] (M₀ : Model K₀ M.pair) : Model K₀ X where
  pair := M₀.pair
  embedding := M.embedding.comp M₀.embedding
  embedding_algebraMap c := by
    rw [RingHom.comp_apply, M₀.embedding_algebraMap, M.embedding_algebraMap,
      IsScalarTower.algebraMap_apply K₀ K k]
  embedding_algebraMap_X := by
    rw [RingHom.comp_apply, M₀.embedding_algebraMap_X, M.embedding_algebraMap_X]
  adjoin_range_embedding := by
    -- `trans` is `@[expose]`, so this proof cannot reference the `private` helpers below.
    let _ : Algebra M.pair X := M.embedding.toAlgebra
    let _ : Algebra K X := ((algebraMap k X).comp (algebraMap K k)).toAlgebra
    have : IsScalarTower K M.pair X := .of_algebraMap_eq fun c ↦ (M.embedding_algebraMap c).symm
    have : IsScalarTower K k X := .of_algebraMap_eq fun _ ↦ rfl
    simpa only [RingHom.algebraMap_toAlgebra, ← Set.range_comp, ← RingHom.coe_comp] using
      adjoin_image_eq_top_of_constantCompositum_eq_top M₀.adjoin_range_embedding
        (constantCompositum_eq_top_of_adjoin_eq_top M.pair k X M.adjoin_range_embedding)

/-- For any field extension `k / K` (algebraic or transcendental), the tensor product
`M.pair ⊗[K] k` of a model with `k` is an integral domain. -/
instance isDomain_tensorProduct : IsDomain (M.pair ⊗[K] k) :=
  isDomain_tensorProduct_of_isGeometricallyReduced
    M.pair.isAlgebraicBelyiPair.isIntegrallyClosedIn k

/-- Symmetric form `IsDomain (k ⊗[K] M.pair)`, convenient because `k ⊗[K] M.pair` carries a global
`k`-algebra structure. -/
instance isDomain_tensorProduct_left : IsDomain (k ⊗[K] M.pair) :=
  isDomain_tensorProduct_of_isGeometricallyReduced_right
    M.pair.isAlgebraicBelyiPair.isIntegrallyClosedIn k

section BaseChange

/-- Induced `K`-algebra structure on `X` along `K → k → X`. -/
private noncomputable abbrev baseAlgebra (K : Type v) [Field K] [Algebra K k]
    (X : AlgebraicBelyiPair k) : Algebra K X :=
  ((algebraMap k X).comp (algebraMap K k)).toAlgebra

/-- Induced `M.pair`-algebra structure on `X` via `M.embedding`. -/
private abbrev pairAlgebra : Algebra M.pair X :=
  M.embedding.toAlgebra

/-- Scalar-tower compatibilities for `baseAlgebra` and `pairAlgebra`. -/
private theorem isScalarTowers :
    letI := baseAlgebra K X
    letI := M.pairAlgebra
    IsScalarTower K M.pair X ∧ IsScalarTower K k X :=
  letI := baseAlgebra K X
  letI := M.pairAlgebra
  ⟨.of_algebraMap_eq fun c ↦ (M.embedding_algebraMap c).symm, .of_algebraMap_eq fun _ ↦ rfl⟩

/-- The compositum of the model with the constants `k`, formed with the embedding of the model,
is the whole function field of `X`. -/
private theorem constantCompositum_eq_top :
    letI := M.pairAlgebra
    constantCompositum M.pair k X = ⊤ :=
  letI := M.pairAlgebra
  constantCompositum_eq_top_of_adjoin_eq_top M.pair k X M.adjoin_range_embedding

/-- Multiplication `M.pair ⊗[K] k →ₐ[K] X` induced by the model embedding and scalar map. -/
private noncomputable abbrev tensorProductMap :
    letI := baseAlgebra K X
    M.pair ⊗[K] k →ₐ[K] X :=
  letI := baseAlgebra K X
  letI := M.pairAlgebra
  haveI := M.isScalarTowers.1
  haveI := M.isScalarTowers.2
  Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom K M.pair X)
    (IsScalarTower.toAlgHom K k X)

/-- Induced `(M.pair ⊗[K] k)`-algebra structure on `X` via multiplication. -/
private noncomputable abbrev tensorAlgebra : Algebra (M.pair ⊗[K] k) X :=
  letI := baseAlgebra K X
  M.tensorProductMap.toRingHom.toAlgebra

private theorem algebraMap_tensorAlgebra_tmul (y : M.pair) (c : k) :
    letI := M.tensorAlgebra
    algebraMap (M.pair ⊗[K] k) X (y ⊗ₜ c) = M.embedding y * algebraMap k X c := by
  let _ := baseAlgebra K X
  let _ := M.pairAlgebra
  obtain ⟨_, _⟩ := M.isScalarTowers
  simp [RingHom.algebraMap_toAlgebra]

private theorem isScalarTower_tensor :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := M.pair) (B := k)
    letI := M.tensorAlgebra
    IsScalarTower k (M.pair ⊗[K] k) X :=
  letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := M.pair) (B := k)
  letI := M.tensorAlgebra
  .of_algebraMap_eq fun c ↦ by
    change algebraMap k X c = algebraMap (M.pair ⊗[K] k) X (1 ⊗ₜ c)
    rw [M.algebraMap_tensorAlgebra_tmul, map_one, one_mul]

/-- Auxiliary `IsFractionRing (M.pair ⊗[K] k) X` along multiplication. -/
private theorem isFractionRing_tensorProduct :
    letI := M.tensorAlgebra
    IsFractionRing (M.pair ⊗[K] k) X := by
  let _ := baseAlgebra K X
  let _ := M.pairAlgebra
  obtain ⟨_, _⟩ := M.isScalarTowers
  exact isFractionRing_tensorProduct_of_linearDisjoint
    (linearDisjoint_of_isGeometricallyReduced_ratFunc
      M.pair.isAlgebraicBelyiPair.isIntegrallyClosedIn M.embedding_algebraMap_X)
    M.constantCompositum_eq_top

/-- For any field extension `k / K` (algebraic or transcendental), the fraction field of
`k ⊗[K] M.pair` is canonically isomorphic to `X` as a `k`-algebra. -/
noncomputable def fractionRingEquiv : FractionRing (k ⊗[K] M.pair) ≃ₐ[k] X :=
  letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := M.pair) (B := k)
  haveI := Algebra.TensorProduct.right_isScalarTower (R := K) (A := M.pair) (B := k)
  letI := M.tensorAlgebra
  haveI := M.isScalarTower_tensor
  haveI := M.isFractionRing_tensorProduct
  (fractionRingTensorCommAlgEquiv K M.pair k X (FractionRing (k ⊗[K] M.pair))).symm

@[simp]
theorem fractionRingEquiv_algebraMap_tmul (c : k) (y : M.pair) :
    M.fractionRingEquiv (algebraMap (k ⊗[K] M.pair) _ (c ⊗ₜ y)) =
      M.embedding y * algebraMap k X c := by
  let _ := Algebra.TensorProduct.rightAlgebra (R := K) (A := M.pair) (B := k)
  have := Algebra.TensorProduct.right_isScalarTower (R := K) (A := M.pair) (B := k)
  let _ := M.tensorAlgebra
  have := M.isScalarTower_tensor
  have := M.isFractionRing_tensorProduct
  rw [fractionRingEquiv, fractionRingTensorCommAlgEquiv_symm_algebraMap_tensorProduct,
    Algebra.TensorProduct.comm_tmul, M.algebraMap_tensorAlgebra_tmul]

/-- The inverse of `fractionRingEquiv` sends `M.embedding y` to the image of `1 ⊗ₜ y`. -/
@[simp]
theorem fractionRingEquiv_symm_embedding (y : M.pair) :
    M.fractionRingEquiv.symm (M.embedding y) =
      algebraMap (k ⊗[K] M.pair) (FractionRing (k ⊗[K] M.pair)) (1 ⊗ₜ y) := by
  rw [AlgEquiv.symm_apply_eq, fractionRingEquiv_algebraMap_tmul, map_one, mul_one]

/-- **Degree invariance for models**: over any extension `k / K` (algebraic or transcendental),
a model `M.pair` over `K` has the same degree over `K(t)` as `X` has over `k(t)`. -/
@[simp]
theorem finrank_pair :
    Module.finrank (RatFunc K) M.pair = Module.finrank (RatFunc k) X := by
  let _ := baseAlgebra K X
  let _ := M.pairAlgebra
  obtain ⟨_, _⟩ := M.isScalarTowers
  exact (finrank_ratFunc_eq_of_isGeometricallyReduced
    M.pair.isAlgebraicBelyiPair.isIntegrallyClosedIn M.constantCompositum_eq_top
    M.embedding_algebraMap_X).symm

/-- The **base change** of a model `Y = (F₀, t)` over `K` of `X = (F, t)` to an algebraic
extension `k` of `K` is `X`: multiplication `F₀ ⊗[K] k → F` is an isomorphism. -/
noncomputable def baseChangeEquiv [Algebra.IsAlgebraic K k] : M.pair ⊗[K] k ≃+* X :=
  letI := baseAlgebra K X
  letI := M.pairAlgebra
  haveI := M.isScalarTowers.1
  haveI := M.isScalarTowers.2
  RingEquiv.ofBijective M.tensorProductMap
    (productMap_bijective_of_constantCompositum_eq_top M.constantCompositum_eq_top)

/-- The isomorphism from the base change of a model is multiplication. -/
@[simp]
theorem baseChangeEquiv_tmul [Algebra.IsAlgebraic K k] (y : M.pair) (c : k) :
    M.baseChangeEquiv (y ⊗ₜ c) = M.embedding y * algebraMap k X c :=
  (rfl)

end BaseChange

@[simp]
theorem baseChangeEquiv_symm_embedding [Algebra.IsAlgebraic K k] (y : M.pair) :
    M.baseChangeEquiv.symm (M.embedding y) = y ⊗ₜ 1 := by
  rw [RingEquiv.symm_apply_eq, baseChangeEquiv_tmul, map_one, mul_one]

@[simp]
theorem baseChangeEquiv_symm_algebraMap [Algebra.IsAlgebraic K k] (c : k) :
    M.baseChangeEquiv.symm (algebraMap k X c) = 1 ⊗ₜ c := by
  rw [RingEquiv.symm_apply_eq, baseChangeEquiv_tmul, map_one, one_mul]

/-- The automorphism of `X` induced by an automorphism `σ` of `k` over `K` through a model over
`K` (for any extension `k / K`, algebraic or transcendental): it lifts `σ ⊗ id` to
`FractionRing (k ⊗[K] F₀)` and conjugates by `fractionRingEquiv`. It fixes the model
(`TauCeti.AlgebraicBelyiPair.Model.baseChangeAut_embedding`) and applies `σ` to the coefficients
of `k(t)` (`TauCeti.AlgebraicBelyiPair.Model.baseChangeAut_algebraMap_ratFunc`). -/
noncomputable def baseChangeAut (σ : k ≃ₐ[K] k) : X ≃+* X :=
  M.fractionRingEquiv.symm.toRingEquiv.trans <|
    (IsFractionRing.ringEquivOfRingEquiv
      (Algebra.TensorProduct.congr σ (AlgEquiv.refl : M.pair ≃ₐ[K] M.pair)).toRingEquiv).trans
      M.fractionRingEquiv.toRingEquiv

variable (σ : k ≃ₐ[K] k)

/-- The automorphism induced by `σ` through a model fixes the model. -/
@[simp]
theorem baseChangeAut_embedding (y : M.pair) :
    M.baseChangeAut σ (M.embedding y) = M.embedding y := by
  simp [baseChangeAut]

/-- The automorphism induced by `σ` through a model acts on the constants `k` by `σ`. -/
@[simp]
theorem baseChangeAut_algebraMap (c : k) :
    M.baseChangeAut σ (algebraMap k X c) = algebraMap k X (σ c) := by
  have hc : algebraMap k (FractionRing (k ⊗[K] M.pair)) c =
      algebraMap (k ⊗[K] M.pair) (FractionRing (k ⊗[K] M.pair)) (c ⊗ₜ 1) :=
    IsScalarTower.algebraMap_apply k (k ⊗[K] M.pair) (FractionRing (k ⊗[K] M.pair)) c
  simp [baseChangeAut, hc]

/-- The automorphism induced by `σ` through a model applies `σ` to the coefficients of `k(t)`: it
is a semilinear automorphism of the pair over `σ`. -/
@[simp]
theorem baseChangeAut_algebraMap_ratFunc (r : RatFunc k) :
    M.baseChangeAut σ (algebraMap (RatFunc k) X r) =
      algebraMap (RatFunc k) X (RatFunc.mapRingEquiv (σ : k ≃+* k) r) := by
  -- Both sides are ring homomorphisms of `r`; compare them on polynomials, on `C` and on `X`.
  have h : ((M.baseChangeAut σ : X →+* X).comp (algebraMap (RatFunc k) X)).comp
      (algebraMap (Polynomial k) (RatFunc k)) =
      ((algebraMap (RatFunc k) X).comp (RatFunc.mapRingEquiv (σ : k ≃+* k) : RatFunc k →+* _)).comp
      (algebraMap (Polynomial k) (RatFunc k)) := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · simp only [RingHom.comp_apply, RingHom.coe_coe, RatFunc.algebraMap_C,
        ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply, baseChangeAut_algebraMap,
        RatFunc.mapRingEquiv_algebraMap_const, AlgEquiv.coe_toRingEquiv]
    · simp only [RingHom.comp_apply, RingHom.coe_coe,
        RatFunc.algebraMap_X, RatFunc.mapRingEquiv_X, ← embedding_algebraMap_X M,
        baseChangeAut_embedding]
  exact RingHom.congr_fun (IsFractionRing.injective_comp_algebraMap h) r

/-- **The field of a model fixes the class**: if `X` has a model over `K` (for any extension
`k / K`, algebraic or transcendental), then every automorphism of `k` fixing `K` fixes the
isomorphism class of `X`. -/
theorem smul_mk_eq_mk (M : Model K X) {g : k ≃ₐ[ℚ] k}
    (hg : ∀ c : K, g (algebraMap K k c) = algebraMap K k c) :
    g • IsoClass.mk X = IsoClass.mk X := by
  let σ : k ≃ₐ[K] k := AlgEquiv.ofRingEquiv (f := (g : k ≃+* k)) hg
  -- `σ` is `g` viewed as a `K`-algebra automorphism, so undoing `g` and then applying `σ` is the
  -- identity.
  have hσ : (g : k ≃+* k).symm.trans (σ : k ≃+* k) = RingEquiv.refl k := by
    ext c
    rw [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, AlgEquiv.ofRingEquiv_apply,
      RingEquiv.apply_symm_apply, RingEquiv.refl_apply]
  refine IsoClass.smul_mk_eq_mk_iff.mpr
    ⟨AlgEquiv.ofRingEquiv (f := (conjRingEquiv (g : k ≃+* k) X).symm.trans (M.baseChangeAut σ))
      fun r ↦ ?_⟩
  rw [RingEquiv.trans_apply, algebraMap_conj, RingEquiv.symm_apply_apply,
    baseChangeAut_algebraMap_ratFunc, ← RingEquiv.trans_apply, ← RatFunc.mapRingEquiv_trans,
    hσ, RatFunc.mapRingEquiv_refl, RingEquiv.refl_apply]

end Model

namespace IsoClass

variable (K) in
/-- An isomorphism class of algebraic Belyi pairs over `k` is **defined over** a field `K → k`
when one of its representatives has a model over `K`; equivalently every representative has one
(`TauCeti.AlgebraicBelyiPair.IsoClass.isDefinedOver_mk_iff`). -/
def IsDefinedOver (c : IsoClass k) : Prop :=
  ∃ X : AlgebraicBelyiPair k, mk X = c ∧ Nonempty (Model K X)

theorem isDefinedOver_iff {c : IsoClass k} :
    c.IsDefinedOver K ↔ ∃ X : AlgebraicBelyiPair k, mk X = c ∧ Nonempty (Model K X) :=
  Iff.rfl

/-- The class of a pair is defined over `K` exactly when the pair has a model over `K`. -/
@[simp]
theorem isDefinedOver_mk_iff {X : AlgebraicBelyiPair k} :
    (mk X).IsDefinedOver K ↔ Nonempty (Model K X) := by
  refine ⟨fun ⟨Y, hY, ⟨M⟩⟩ ↦ ?_, fun h ↦ ⟨X, rfl, h⟩⟩
  obtain ⟨e⟩ := mk_eq_mk_iff.mp hY
  exact ⟨M.mapAlgEquiv e⟩

/-- Every isomorphism class over `k` is defined over `k`. -/
theorem isDefinedOver_self (c : IsoClass k) : c.IsDefinedOver k := by
  induction c using ind with
  | h X => exact isDefinedOver_mk_iff.mpr ⟨Model.refl X⟩

/-- If a class is defined over a field `K` (algebraic or transcendental under `k`), then every
automorphism of `k` fixing `K` fixes the class. -/
theorem IsDefinedOver.smul_eq {c : IsoClass k} (hc : c.IsDefinedOver K)
    {g : k ≃ₐ[ℚ] k} (hg : ∀ a : K, g (algebraMap K k a) = algebraMap K k a) : g • c = c := by
  obtain ⟨X, rfl, ⟨M⟩⟩ := hc
  exact M.smul_mk_eq_mk hg

/-- **The automorphisms fixing a field of definition stabilize the class**: if a class `c` is
defined over a subfield `K` of `k`, then the automorphisms of `k` fixing `K` pointwise lie in the
stabilizer of `c`. -/
theorem IsDefinedOver.fixingSubgroup_le_stabilizer {K : IntermediateField ℚ k}
    {c : IsoClass k} (hc : c.IsDefinedOver K) :
    K.fixingSubgroup ≤ MulAction.stabilizer (k ≃ₐ[ℚ] k) c :=
  fun g hg ↦ hc.smul_eq fun a ↦ (IntermediateField.mem_fixingSubgroup_iff K g).mp hg a a.property

/-- **Every field of definition contains the field of moduli**: if a class `c` is defined over a
subfield `K` of `k` over which `k` is Galois, such as a number field inside
`AlgebraicClosure ℚ`, then the field of moduli of `c` is contained in `K`. -/
theorem IsDefinedOver.fieldOfModuli_le {K : IntermediateField ℚ k} [IsGalois K k]
    {c : IsoClass k} (hc : c.IsDefinedOver K) : c.fieldOfModuli ≤ K :=
  fieldOfModuli_le_of_fixingSubgroup_le hc.fixingSubgroup_le_stabilizer

end IsoClass

end AlgebraicBelyiPair

end TauCeti
