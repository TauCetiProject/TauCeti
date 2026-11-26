/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.FieldOfModuli
public import Mathlib.RingTheory.TensorProduct.Basic
import TauCeti.FieldTheory.AlgebraicClosure
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Parameter
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Regular
import TauCeti.FieldTheory.FunctionField.ConstantExtension.TensorProduct
public import TauCeti.FieldTheory.RatFunc.Map
import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Models of algebraic Belyi pairs and fields of definition

Let `X = (F, k(t) ↪ F)` be an algebraic Belyi pair over a field `k` of characteristic zero, such
as `AlgebraicClosure ℚ`, and let `K → k` be a field extension, such as a number field inside
`AlgebraicClosure ℚ`. A **model** of `X` over `K` is an algebraic Belyi pair `Y = (F₀, K(t) ↪ F₀)`
over `K` together with an embedding `F₀ ↪ F` which is the given map on the constants, sends `t`
to `t`, and whose image generates `F` over `k`. When `k / K` is arbitrary (possibly
transcendental), `F` is still isomorphic to the fraction field of `F₀ ⊗[K] k`
(`TauCeti.AlgebraicBelyiPair.Model.fractionRingEquiv`) and multiplication
identifies `k(t) ⊗[K(t)] F₀` with `F`
(`TauCeti.AlgebraicBelyiPair.Model.ratFuncBaseChangeEquiv`), using the canonical
coefficient-extension map `TauCeti.ratFuncMapRingHom K k : K(t) →+* k(t)` fixing `t` (with its
compatible `K`-scalar tower), preserving the Belyi degree
(`TauCeti.AlgebraicBelyiPair.Model.finrank_pair`). When `k / K` is algebraic, multiplication
identifies the base change `F₀ ⊗[K] k` with `F`
(`TauCeti.AlgebraicBelyiPair.Model.baseChangeEquiv`): the exact constant field `K` of `F₀` makes
the tensor product a field, and the generation hypothesis makes multiplication onto. So a model
is an algebraic Belyi pair over `K` whose base change to `k` recovers `X` (as the tensor product
for algebraic `k / K`, and as its fraction field in general). An isomorphism class of pairs over
`k` is **defined over** `K` when one, equivalently every, representative has a model over `K`.

Even for an arbitrary (possibly transcendental) extension `k / K`, a model makes every automorphism
`σ` of `k` over `K` act on `F`, by extending `id ⊗ σ` on `F₀ ⊗[K] k` to the fraction field and
transporting along `TauCeti.AlgebraicBelyiPair.Model.fractionRingEquiv`
(`TauCeti.AlgebraicBelyiPair.Model.baseChangeAut`). This automorphism fixes the model and `t`,
and applies `σ` to the coefficients of `k(t)`, so it is an isomorphism of pairs from the
conjugate `X^σ` to `X`. Hence the automorphisms of `k` fixing `K` stabilize the class of `X`
(`TauCeti.AlgebraicBelyiPair.Model.smul_mk_eq_mk`), and when `k / K` is Galois, the field of
moduli of the class is contained in `K`: **every field of definition `K` for which `k / K` is
Galois contains the field of moduli**. The converse fails in general: a class need not be defined
over its field of moduli (Couveignes).

## Main definitions

* `TauCeti.AlgebraicBelyiPair.Model`: a model of an algebraic Belyi pair over a subfield.
* `TauCeti.AlgebraicBelyiPair.Model.fractionRingEquiv`: the fraction-field base-change isomorphism
  `FractionRing (F₀ ⊗[K] k) ≃+* F` for an arbitrary extension `k / K`.
* `TauCeti.AlgebraicBelyiPair.Model.ratFuncBaseChangeEquiv`: the parameter base-change isomorphism
  `k(t) ⊗[K(t)] F₀ ≃ₐ[k(t)] F` using the canonical coefficient-extension map
  `TauCeti.ratFuncMapRingHom K k` fixing `t` (with its compatible `K`-scalar tower), for an
  arbitrary extension `k / K`.
* `TauCeti.AlgebraicBelyiPair.Model.baseChangeEquiv`: the isomorphism from the base change of a
  model onto the pair when `k / K` is algebraic.
* `TauCeti.AlgebraicBelyiPair.Model.baseChangeAut` and
  `TauCeti.AlgebraicBelyiPair.Model.baseChangeAutHom`: the automorphism of the pair induced by an
  automorphism of the constants fixing the field of the model, for an arbitrary extension `k / K`.
* `TauCeti.AlgebraicBelyiPair.IsoClass.IsDefinedOver`: an isomorphism class is defined over a
  subfield.

## Main results

* `TauCeti.AlgebraicBelyiPair.Model.isDomain_tensorProduct`: the tensor product `F₀ ⊗[K] k` of a
  model with an arbitrary constant extension is a domain.
* `TauCeti.AlgebraicBelyiPair.Model.finrank_pair`: every model has the same Belyi degree as `X`.
* `TauCeti.AlgebraicBelyiPair.Model.smul_mk_eq_mk`: an automorphism of `k` fixing the field of a
  model fixes the class of the pair, with no algebraicity assumption on `k / K`.
* `TauCeti.AlgebraicBelyiPair.IsoClass.IsDefinedOver.fieldOfModuli_le`: the field of moduli of a
  class is contained in every field of definition over which `k` is Galois.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  Section 1 and (2.1) Definition.
* J.-M. Couveignes, *Calcul et rationalité de fonctions de Belyi en genre 0*, Annales de
  l'Institut Fourier 44 (1994), 1–38, for Belyi maps not defined over their field of moduli.
-/

public section

universe u v

open scoped TensorProduct

namespace TauCeti

namespace AlgebraicBelyiPair

variable {k : Type u} [Field k] [CharZero k]

/-- The `RatFunc K`-algebra structure on `X` induced by `K(t) → k(t) → X` via
`TauCeti.ratFuncMapRingHom K k`. -/
@[expose, instance_reducible]
noncomputable def ratFuncAlgebra (X : AlgebraicBelyiPair k) (K : Type v) [Field K] [Algebra K k] :
    Algebra (RatFunc K) X :=
  ((algebraMap (RatFunc k) X).comp (ratFuncMapRingHom K k)).toAlgebra

variable {K : Type v} [Field K] [CharZero K] [Algebra K k]

variable (K) in
/-- A **model** of an algebraic Belyi pair `X = (F, k(t) ↪ F)` over a field `K → k`: an algebraic
Belyi pair `Y = (F₀, K(t) ↪ F₀)` over `K` with an embedding `F₀ ↪ F` that is the map `K → k` on
the constants, sends `t` to `t`, and whose image generates `F` over `k`. For algebraic `k / K` it
identifies the base change `F₀ ⊗[K] k` with `F`
(`TauCeti.AlgebraicBelyiPair.Model.baseChangeEquiv`). -/
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

/-- The `M.pair`-algebra structure on `X` induced by `M.embedding`. -/
@[instance_reducible]
private def pairAlgebra : Algebra M.pair X := M.embedding.toAlgebra

/-- The `K`-algebra structure on `X` induced by `K → k → X`. -/
@[instance_reducible]
private def constAlgebra (K : Type v) [Field K] [Algebra K k] (X : AlgebraicBelyiPair k) :
    Algebra K X :=
  ((algebraMap k X).comp (algebraMap K k)).toAlgebra

private theorem isScalarTower_pair :
    letI := M.pairAlgebra
    letI := constAlgebra K X
    IsScalarTower K M.pair X :=
  letI := M.pairAlgebra
  letI := constAlgebra K X
  .of_algebraMap_eq fun c ↦ (M.embedding_algebraMap c).symm

private theorem isScalarTower_const (K : Type v) [Field K] [Algebra K k]
    (X : AlgebraicBelyiPair k) :
    letI := constAlgebra K X
    IsScalarTower K k X :=
  letI := constAlgebra K X
  .of_algebraMap_eq fun _ ↦ rfl

/-- The compositum of the model with the constants `k`, formed with the embedding of the model,
is the whole function field of `X`. -/
private theorem constantCompositum_eq_top :
    letI := M.pairAlgebra
    constantCompositum M.pair k X = ⊤ :=
  letI := M.pairAlgebra
  (constantCompositum_eq_top_iff_adjoin_range_eq_top M.pair k X).mpr M.adjoin_range_embedding

/-- A model of `X` is linearly disjoint from `k` over `K` inside `X`, with no algebraicity
hypothesis on `k / K`. -/
private theorem linearDisjoint :
    letI := M.pairAlgebra
    letI := constAlgebra K X
    haveI := M.isScalarTower_pair
    haveI := isScalarTower_const K X
    (IsScalarTower.toAlgHom K k X).fieldRange.LinearDisjoint M.pair := by
  let _ := M.pairAlgebra
  let _ := constAlgebra K X
  have _ := M.isScalarTower_pair
  have _ := isScalarTower_const K X
  exact linearDisjoint_of_isGeometricallyReduced_ratFunc
    M.pair.isAlgebraicBelyiPair.isIntegrallyClosedIn M.embedding_algebraMap_X

/-- The base change `M.pair ⊗[K] k` of a model over `K` to an arbitrary extension `k` is an
integral domain. -/
theorem isDomain_tensorProduct : IsDomain (M.pair ⊗[K] k) :=
  isDomain_tensorProduct_of_isGeometricallyReduced
    M.pair.isAlgebraicBelyiPair.isIntegrallyClosedIn k

/-- The multiplication map `M.pair ⊗[K] k →ₐ[K] X` induced by a model. -/
private noncomputable def tensorProductMap :
    letI := constAlgebra K X
    M.pair ⊗[K] k →ₐ[K] X :=
  letI := M.pairAlgebra
  letI := constAlgebra K X
  haveI := M.isScalarTower_pair
  haveI := isScalarTower_const K X
  Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom K M.pair X)
    (IsScalarTower.toAlgHom K k X)

private theorem tensorProductMap_tmul (y : M.pair) (c : k) :
    M.tensorProductMap (y ⊗ₜ c) = M.embedding y * algebraMap k X c := by
  let _ := M.pairAlgebra
  let _ := constAlgebra K X
  have _ := M.isScalarTower_pair
  have _ := isScalarTower_const K X
  exact Algebra.TensorProduct.productMap_apply_tmul _ _ y c

/-- The `(M.pair ⊗[K] k)`-algebra structure on `X` induced by `M.tensorProductMap`. -/
@[instance_reducible]
private noncomputable def tensorProductAlgebra :
    letI := constAlgebra K X
    Algebra (M.pair ⊗[K] k) X :=
  letI := constAlgebra K X
  M.tensorProductMap.toRingHom.toAlgebra

/-- The localization equivalence `FractionRing (M.pair ⊗[K] k) ≃ₐ[M.pair ⊗[K] k] X` for the
shared tensor-product algebra structure. -/
private noncomputable def fractionRingAlgEquiv :
    letI := constAlgebra K X
    letI := M.tensorProductAlgebra
    FractionRing (M.pair ⊗[K] k) ≃ₐ[M.pair ⊗[K] k] X :=
  letI := M.pairAlgebra
  letI := constAlgebra K X
  haveI := M.isScalarTower_pair
  haveI := isScalarTower_const K X
  letI := M.tensorProductAlgebra
  haveI : IsFractionRing (M.pair ⊗[K] k) X :=
    isFractionRing_tensorProduct_of_linearDisjoint M.linearDisjoint M.constantCompositum_eq_top
  haveI : IsDomain (M.pair ⊗[K] k) := M.isDomain_tensorProduct
  IsLocalization.algEquiv (nonZeroDivisors (M.pair ⊗[K] k)) (FractionRing (M.pair ⊗[K] k)) X

/-- **Fraction-field base change of a model**: for an arbitrary extension `k / K` (possibly
transcendental), `X` is canonically isomorphic to `FractionRing (M.pair ⊗[K] k)`. -/
noncomputable def fractionRingEquiv : FractionRing (M.pair ⊗[K] k) ≃+* X :=
  letI := constAlgebra K X
  letI := M.tensorProductAlgebra
  M.fractionRingAlgEquiv.toRingEquiv

/-- On the image of a pure tensor `y ⊗ₜ c` in `FractionRing (M.pair ⊗[K] k)`,
`M.fractionRingEquiv` is `M.embedding y * algebraMap k X c`. -/
@[simp]
theorem fractionRingEquiv_algebraMap_tmul (y : M.pair) (c : k) :
    M.fractionRingEquiv
        (algebraMap (M.pair ⊗[K] k) (FractionRing (M.pair ⊗[K] k)) (y ⊗ₜ c)) =
      M.embedding y * algebraMap k X c := by
  let _ := constAlgebra K X
  let _ := M.tensorProductAlgebra
  rw [fractionRingEquiv, AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes]
  exact M.tensorProductMap_tmul y c

@[simp]
theorem fractionRingEquiv_symm_embedding (y : M.pair) :
    M.fractionRingEquiv.symm (M.embedding y) =
      algebraMap (M.pair ⊗[K] k) (FractionRing (M.pair ⊗[K] k)) (y ⊗ₜ 1) := by
  rw [RingEquiv.symm_apply_eq, fractionRingEquiv_algebraMap_tmul, map_one, mul_one]

@[simp]
theorem fractionRingEquiv_symm_algebraMap (c : k) :
    M.fractionRingEquiv.symm (algebraMap k X c) =
      algebraMap (M.pair ⊗[K] k) (FractionRing (M.pair ⊗[K] k)) (1 ⊗ₜ c) := by
  rw [RingEquiv.symm_apply_eq, fractionRingEquiv_algebraMap_tmul, map_one, one_mul]

/-- **Parameter base change of a model**: for an arbitrary extension `k / K` (possibly
transcendental), multiplication identifies `RatFunc k ⊗[RatFunc K] M.pair` with `X` as
`RatFunc k`-algebras, using the canonical coefficient-extension map `TauCeti.ratFuncMapRingHom K k`
fixing `t` (with its compatible `K`-scalar tower). -/
noncomputable def ratFuncBaseChangeEquiv :
    letI : Algebra (RatFunc K) (RatFunc k) := (ratFuncMapRingHom K k).toAlgebra
    RatFunc k ⊗[RatFunc K] M.pair ≃ₐ[RatFunc k] X :=
  letI : Algebra (RatFunc K) (RatFunc k) := (ratFuncMapRingHom K k).toAlgebra
  haveI : IsScalarTower K (RatFunc K) (RatFunc k) :=
    TauCeti.RatFunc.isScalarTower_of_algebraMap_C (ratFuncMapRingHom_C K k)
  letI := M.pairAlgebra
  letI := constAlgebra K X
  haveI := M.isScalarTower_pair
  haveI := isScalarTower_const K X
  constantExtensionRatFuncTensorEquiv M.linearDisjoint M.constantCompositum_eq_top
    (ratFuncMapRingHom_X K k) M.embedding_algebraMap_X

/-- On pure tensors, `ratFuncBaseChangeEquiv` multiplies the `k(t)` scalar and the model
embedding. -/
@[simp]
theorem ratFuncBaseChangeEquiv_tmul (r : RatFunc k) (y : M.pair) :
    letI : Algebra (RatFunc K) (RatFunc k) := (ratFuncMapRingHom K k).toAlgebra
    M.ratFuncBaseChangeEquiv (r ⊗ₜ[RatFunc K] y) =
      algebraMap (RatFunc k) X r * M.embedding y :=
  letI : Algebra (RatFunc K) (RatFunc k) := (ratFuncMapRingHom K k).toAlgebra
  haveI : IsScalarTower K (RatFunc K) (RatFunc k) :=
    TauCeti.RatFunc.isScalarTower_of_algebraMap_C (ratFuncMapRingHom_C K k)
  letI := M.pairAlgebra
  letI := constAlgebra K X
  haveI := M.isScalarTower_pair
  haveI := isScalarTower_const K X
  constantExtensionRatFuncTensorEquiv_tmul M.linearDisjoint M.constantCompositum_eq_top
    (ratFuncMapRingHom_X K k) M.embedding_algebraMap_X r y

/-- The inverse of `ratFuncBaseChangeEquiv` maps the embedding of a model element `y` to
`1 ⊗ₜ y`. -/
@[simp]
theorem ratFuncBaseChangeEquiv_symm_embedding (y : M.pair) :
    letI : Algebra (RatFunc K) (RatFunc k) := (ratFuncMapRingHom K k).toAlgebra
    M.ratFuncBaseChangeEquiv.symm (M.embedding y) = 1 ⊗ₜ[RatFunc K] y := by
  let _ : Algebra (RatFunc K) (RatFunc k) := (ratFuncMapRingHom K k).toAlgebra
  rw [AlgEquiv.symm_apply_eq, ratFuncBaseChangeEquiv_tmul, map_one, one_mul]

/-- Every model of `X` has the same Belyi degree as `X`, with no algebraicity assumption on
`k / K`. -/
@[simp]
theorem finrank_pair : Module.finrank (RatFunc K) M.pair = Module.finrank (RatFunc k) X :=
  letI := M.pairAlgebra
  letI := constAlgebra K X
  haveI := M.isScalarTower_pair
  haveI := isScalarTower_const K X
  (finrank_ratFunc_eq_of_isGeometricallyReduced
    M.pair.isAlgebraicBelyiPair.isIntegrallyClosedIn M.constantCompositum_eq_top
    M.embedding_algebraMap_X).symm

/-- The **base change** of a model `Y = (F₀, t)` over `K` of `X = (F, t)` to an algebraic
extension `k` of `K` is `X`: multiplication `F₀ ⊗[K] k → F` is an isomorphism. -/
noncomputable def baseChangeEquiv [Algebra.IsAlgebraic K k] : M.pair ⊗[K] k ≃+* X :=
  letI := M.pairAlgebra
  letI := constAlgebra K X
  haveI := M.isScalarTower_pair
  haveI := isScalarTower_const K X
  haveI : IsDomain (M.pair ⊗[K] k) := M.isDomain_tensorProduct
  RingEquiv.ofBijective M.tensorProductMap
    (productMap_bijective_of_constantCompositum_eq_top M.constantCompositum_eq_top)

/-- The isomorphism from the base change of a model is multiplication. -/
@[simp]
theorem baseChangeEquiv_tmul [Algebra.IsAlgebraic K k] (y : M.pair) (c : k) :
    M.baseChangeEquiv (y ⊗ₜ c) = M.embedding y * algebraMap k X c :=
  M.tensorProductMap_tmul y c

@[simp]
theorem baseChangeEquiv_symm_embedding [Algebra.IsAlgebraic K k] (y : M.pair) :
    M.baseChangeEquiv.symm (M.embedding y) = y ⊗ₜ 1 := by
  rw [RingEquiv.symm_apply_eq, baseChangeEquiv_tmul, map_one, mul_one]

@[simp]
theorem baseChangeEquiv_symm_algebraMap [Algebra.IsAlgebraic K k] (c : k) :
    M.baseChangeEquiv.symm (algebraMap k X c) = 1 ⊗ₜ c := by
  rw [RingEquiv.symm_apply_eq, baseChangeEquiv_tmul, map_one, one_mul]

/-- Two ring homomorphisms out of `X` agreeing on a model `M.embedding` and on the constants
`algebraMap k X` are equal. -/
theorem ringHom_ext {R : Type*} [Semiring R] {f g : X →+* R}
    (h₁ : ∀ y : M.pair, f (M.embedding y) = g (M.embedding y))
    (h₂ : ∀ c : k, f (algebraMap k X c) = g (algebraMap k X c)) : f = g := by
  refine RingHom.eq_of_eqOn_of_field_closure_eq_top
    (s := Set.range (algebraMap k X) ∪ Set.range M.embedding) ?_ ?_
  · rw [← IntermediateField.adjoin_toSubfield, M.adjoin_range_embedding,
      IntermediateField.top_toSubfield]
  · rintro _ (⟨c, rfl⟩ | ⟨y, rfl⟩)
    · exact h₂ c
    · exact h₁ y

/-- The automorphism of `X` induced by an automorphism `σ` of `k` over `K` through a model over
`K`: it is `id ⊗ σ` extended to the fraction field of `F₀ ⊗[K] k` and transported along
`M.fractionRingEquiv`. It fixes the model
(`TauCeti.AlgebraicBelyiPair.Model.baseChangeAut_embedding`) and applies `σ` to the coefficients
of `k(t)` (`TauCeti.AlgebraicBelyiPair.Model.baseChangeAut_algebraMap_ratFunc`). -/
noncomputable def baseChangeAut (σ : k ≃ₐ[K] k) : X ≃+* X :=
  haveI : IsDomain (M.pair ⊗[K] k) := M.isDomain_tensorProduct
  M.fractionRingEquiv.symm.trans <|
    (IsFractionRing.ringEquivOfRingEquiv
      (Algebra.TensorProduct.congr (AlgEquiv.refl : M.pair ≃ₐ[K] M.pair) σ).toRingEquiv).trans
      M.fractionRingEquiv

section BaseChangeAut

variable (σ τ : k ≃ₐ[K] k)

/-- The automorphism induced by `σ` through a model fixes the model. -/
@[simp]
theorem baseChangeAut_embedding (y : M.pair) :
    M.baseChangeAut σ (M.embedding y) = M.embedding y := by
  simp [baseChangeAut]

/-- The automorphism induced by `σ` through a model acts on the constants `k` by `σ`. -/
@[simp]
theorem baseChangeAut_algebraMap (c : k) :
    M.baseChangeAut σ (algebraMap k X c) = algebraMap k X (σ c) := by
  simp [baseChangeAut]

/-- The automorphism induced by `1` through a model is the identity. -/
@[simp]
theorem baseChangeAut_one : M.baseChangeAut 1 = RingEquiv.refl X :=
  RingEquiv.toRingHom_injective <| M.ringHom_ext (fun y ↦ by simp) fun c ↦ by simp

/-- Composition of model-induced automorphisms (in `RingEquiv.trans` order). -/
theorem baseChangeAut_trans :
    M.baseChangeAut (σ.trans τ) = (M.baseChangeAut σ).trans (M.baseChangeAut τ) :=
  RingEquiv.toRingHom_injective <| M.ringHom_ext (fun y ↦ by simp) fun c ↦ by simp

/-- Multiplication of model-induced automorphisms in `Aut(k/K)` matches `RingAut X`
multiplication. -/
theorem baseChangeAut_mul : M.baseChangeAut (σ * τ) = M.baseChangeAut σ * M.baseChangeAut τ :=
  RingEquiv.toRingHom_injective <| M.ringHom_ext (fun y ↦ by simp [RingAut.mul_apply])
    fun c ↦ by simp [RingAut.mul_apply]

/-- The inverse of a model-induced automorphism is induced by `σ⁻¹`. -/
@[simp]
theorem baseChangeAut_symm : (M.baseChangeAut σ).symm = M.baseChangeAut σ.symm :=
  RingEquiv.toRingHom_injective <| M.ringHom_ext
    (fun y ↦ by
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq,
        baseChangeAut_embedding])
    fun c ↦ by
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq,
        baseChangeAut_algebraMap, AlgEquiv.apply_symm_apply]

/-- The group homomorphism `(k ≃ₐ[K] k) →* RingAut X` induced by a model over `K`. -/
@[expose, simps]
noncomputable def baseChangeAutHom : (k ≃ₐ[K] k) →* RingAut X where
  toFun := M.baseChangeAut
  map_one' := M.baseChangeAut_one
  map_mul' := M.baseChangeAut_mul

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

end BaseChangeAut

/-- **The field of a model fixes the class**: if `X` has a model over `K` (for an arbitrary,
possibly transcendental extension `k / K`), then every automorphism of `k` fixing `K` fixes the
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

/-- An isomorphism class defined over an intermediate field `K₀` is also defined over
`IntermediateField.extendScalars h`. -/
theorem IsDefinedOver.extendScalars {F : Type*} [Field F] [Algebra F k]
    {F' K₀ : IntermediateField F k} (h : F' ≤ K₀) {c : IsoClass k} (hc : c.IsDefinedOver K₀) :
    c.IsDefinedOver (IntermediateField.extendScalars h) :=
  hc

/-- If a class is defined over a field `K`, then every automorphism of `k` fixing `K` fixes the
class. -/
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

/-- **Every field of definition `K` for which `k / K` is Galois contains the field of moduli**: if
a class `c` is defined over a subfield `K` of `k` over which `k` is Galois, such as a number field
inside `AlgebraicClosure ℚ`, then the field of moduli of `c` is contained in `K`. -/
theorem IsDefinedOver.fieldOfModuli_le {K : IntermediateField ℚ k} [IsGalois K k]
    {c : IsoClass k} (hc : c.IsDefinedOver K) : c.fieldOfModuli ≤ K :=
  fieldOfModuli_le_of_fixingSubgroup_le hc.fixingSubgroup_le_stabilizer

end IsoClass

end AlgebraicBelyiPair

end TauCeti
