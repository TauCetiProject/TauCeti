/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Model
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.GaloisDescent
public import TauCeti.FieldTheory.RatFunc.Transcendental
import TauCeti.FieldTheory.FunctionField.Belyi.BaseChange

/-!
# Weil descent of algebraic Belyi pairs

Let `L / K` be a finite Galois extension of fields of characteristic zero, and let `X = (F, t)` be
an algebraic Belyi pair over `L`. A **descent datum** for `X` relative to `K` is a family of
isomorphisms of pairs `f_σ : X^σ ≃ X`, one for each `σ ∈ Gal(L/K)`, from the conjugate of `X`
along `σ` to `X`, satisfying the cocycle condition `f_{στ} = f_σ ∘ σ(f_τ)`. This is Weil's
criterion for the field of definition of a variety, applied to the function field of the curve
together with its Belyi map. Every descent datum is effective: it produces an algebraic Belyi
pair over `K` whose base change to `L` is `X`.

All conjugates of `X` have the same underlying field `F`, so each `f_σ` is a ring automorphism of
`F`. It acts on the constants `L` by `σ` and fixes `t`, and the cocycle condition says that
`σ ↦ f_σ` is a group homomorphism (`TauCeti.AlgebraicBelyiPair.DescentDatum.semilinearAction`).
Galois descent along this semilinear action (`TauCeti.GaloisDescent`) shows that its fixed field
`F₀` has exact constant field `K`, that `F₀ ⊗[K] L ≃ F`, and that `F` is the compositum
`F₀ · L`. Since `t` is fixed, it lies in `F₀`, and the base-change comparison of Belyi pairs
(`TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`) shows that `F₀` over `K(t)` is
an algebraic Belyi pair of the same degree
(`TauCeti.GaloisDescent.isAlgebraicBelyiPair_fixedField_iff`). Embedded in `F` as the fixed field,
the descended pair is a model of `X` over `K` in the sense of `TauCeti.AlgebraicBelyiPair.Model`
(`TauCeti.AlgebraicBelyiPair.DescentDatum.model`), so a class admitting a descent datum is defined
over `K`.

A family of isomorphisms that is not a cocycle need not descend: whether the isomorphisms
`f_σ` can be chosen to form a cocycle is the gap between the field of moduli of a Belyi pair and
its fields of definition.

## Main definitions

* `TauCeti.AlgebraicBelyiPair.DescentDatum`: a descent datum for an algebraic Belyi pair over `L`
  relative to `K`.
* `TauCeti.AlgebraicBelyiPair.DescentDatum.semilinearAction`: the semilinear action of
  `Gal(L/K)` on the function field given by a descent datum.
* `TauCeti.AlgebraicBelyiPair.DescentDatum.descend`: the descended algebraic Belyi pair over `K`.
* `TauCeti.AlgebraicBelyiPair.DescentDatum.baseChangeEquiv`: the base-change isomorphism
  `L ⊗[K] F₀ ≃ F`.
* `TauCeti.AlgebraicBelyiPair.DescentDatum.model`: the descended pair as a model of `X` over `K`.

## Main results

* `TauCeti.GaloisDescent.isAlgebraicBelyiPair_fixedField_iff`: the fixed field of a semilinear
  action fixing `t` is an algebraic Belyi pair over `K` exactly when `F` is one over `L`.
* `TauCeti.AlgebraicBelyiPair.DescentDatum.algebraMap_descend_X`: the function `t` descends.
* `TauCeti.AlgebraicBelyiPair.DescentDatum.constantCompositum_descend_eq_top` and
  `TauCeti.AlgebraicBelyiPair.DescentDatum.finrank_descend`: the descended pair base-changes back
  to `X`, with the same degree.
* `TauCeti.AlgebraicBelyiPair.DescentDatum.isDefinedOver_mk`: **effectiveness**, a pair with a
  descent datum relative to `K` is defined over `K`.

## References

* A. Weil, *The field of definition of a variety*, American Journal of Mathematics 78 (1956),
  509–524.
* J.-M. Couveignes, *Calcul et rationalité de fonctions de Belyi en genre 0*, Annales de
  l'Institut Fourier 44 (1994), Théorème 3 (critère de Weil).
* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  (1.9) Theorem and (1.10) Lemma.
-/

public section

open IntermediateField

open scoped TensorProduct

universe u

namespace TauCeti

/-! ### Descent along a semilinear action -/

namespace GaloisDescent

variable {K L F : Type*} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F] [Algebra L F]
  [IsScalarTower K L F] [Algebra (RatFunc L) F] [IsScalarTower L (RatFunc L) F]
  [FiniteDimensional K L] [IsGalois K L] {ρ : (L ≃ₐ[K] L) →* (F ≃ₐ[K] F)}
  [Algebra (RatFunc K) (fixedField ρ.range)] [IsScalarTower K (RatFunc K) (fixedField ρ.range)]

/-- **Belyi pairs descend along semilinear actions.** Let `ρ` be a semilinear action of
`Gal(L/K)` on a field `F` finite over `L(t)`, for a finite Galois extension `L / K` of fields of
characteristic zero, and let the variable of `K(t)` act on the fixed field `F₀` of `ρ` as the
variable of `L(t)` acts on `F`. Then `F₀` over `K(t)` is an algebraic Belyi pair exactly when `F`
over `L(t)` is one. -/
theorem isAlgebraicBelyiPair_fixedField_iff [CharZero K] [CharZero L]
    [FiniteDimensional (RatFunc L) F] [FiniteDimensional (RatFunc K) (fixedField ρ.range)]
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hX : algebraMap (fixedField ρ.range) F (algebraMap (RatFunc K) _ RatFunc.X) =
      algebraMap (RatFunc L) F RatFunc.X) :
    IsAlgebraicBelyiPair K (fixedField ρ.range) ↔ IsAlgebraicBelyiPair L F := by
  have hcomp := constantCompositum_fixedField_eq_top hρ
  exact ⟨fun h ↦ (isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top
      h.isIntegrallyClosedIn hcomp hX).mpr h,
    fun h ↦ (isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top
      (isIntegrallyClosedIn_fixedField hρ h.isIntegrallyClosedIn) hcomp hX).mp h⟩

end GaloisDescent

/-! ### Descent data -/

namespace AlgebraicBelyiPair

variable {K L : Type u} [Field K] [Field L] [CharZero L] [Algebra K L]

variable (K) in
/-- A **descent datum** for an algebraic Belyi pair `X` over `L` relative to a subfield `K`: for
each `σ ∈ Gal(L/K)` an isomorphism of pairs `f_σ : X^σ ≃ X` from the conjugate of `X` along `σ`,
satisfying the cocycle condition `f_{στ} = f_σ ∘ σ(f_τ)`.

All conjugates of `X` have the underlying field of `X`, and the conjugate `σ(f_τ)` of `f_τ` is
`f_τ` on that field (`TauCeti.AlgebraicBelyiPair.conjAlgEquiv_conjRingEquiv`), so the cocycle
condition is stated there, as `f_{στ}(x) = f_σ(f_τ(x))`. -/
@[ext]
structure DescentDatum (X : AlgebraicBelyiPair L) where
  /-- The isomorphism `f_σ` from the conjugate of the pair along `σ` to the pair. -/
  iso (σ : L ≃ₐ[K] L) : X.conj (σ : L ≃+* L) ≃ₐ[RatFunc L] X
  /-- The cocycle condition `f_{στ} = f_σ ∘ σ(f_τ)`, on the common underlying field. -/
  iso_mul (σ τ : L ≃ₐ[K] L) (x : X) :
    iso (σ * τ) (conjRingEquiv _ X x) = iso σ (conjRingEquiv _ X (iso τ (conjRingEquiv _ X x)))

namespace DescentDatum

variable {X : AlgebraicBelyiPair L} [Algebra K X] [IsScalarTower K L X] (D : DescentDatum K X)

/-- The **semilinear action** of `Gal(L/K)` on the function field of `X` given by a descent datum:
`σ` acts by the isomorphism `f_σ`, read as an automorphism of the underlying field. It acts on the
constants `L` by `σ` (`TauCeti.AlgebraicBelyiPair.DescentDatum.semilinearAction_algebraMap`), and
the cocycle condition makes it a group homomorphism. -/
noncomputable def semilinearAction : (L ≃ₐ[K] L) →* (X ≃ₐ[K] X) :=
  MonoidHom.mk' (fun σ ↦ AlgEquiv.ofRingEquiv
    (f := (conjRingEquiv (σ : L ≃+* L) X).trans (D.iso σ).toRingEquiv) fun c ↦ by
      simp [IsScalarTower.algebraMap_apply K L X, IsScalarTower.algebraMap_apply L (RatFunc L) X])
    fun σ τ ↦ AlgEquiv.ext fun x ↦ D.iso_mul σ τ x

theorem semilinearAction_apply (σ : L ≃ₐ[K] L) (x : X) :
    D.semilinearAction σ x = D.iso σ (conjRingEquiv _ X x) :=
  (rfl)

/-- The semilinear action of a descent datum acts on `L(t)` by the coefficient map of `σ`. -/
@[simp]
theorem semilinearAction_algebraMap_ratFunc (σ : L ≃ₐ[K] L) (r : RatFunc L) :
    D.semilinearAction σ (algebraMap (RatFunc L) X r) =
      algebraMap (RatFunc L) X (RatFunc.mapRingEquiv (σ : L ≃+* L) r) := by
  rw [semilinearAction_apply, conjRingEquiv_algebraMap_ratFunc, AlgEquiv.commutes]

/-- The semilinear action of a descent datum acts on the constants `L` by `σ`. -/
@[simp]
theorem semilinearAction_algebraMap (σ : L ≃ₐ[K] L) (a : L) :
    D.semilinearAction σ (algebraMap L X a) = algebraMap L X (σ a) := by
  rw [IsScalarTower.algebraMap_apply L (RatFunc L) X, semilinearAction_algebraMap_ratFunc,
    RatFunc.mapRingEquiv_algebraMap_const, AlgEquiv.coe_toRingEquiv,
    ← IsScalarTower.algebraMap_apply]

/-- The Belyi function `t`, as an element of the fixed field of the semilinear action. -/
private noncomputable def gen : fixedField D.semilinearAction.range :=
  ⟨algebraMap (RatFunc L) X RatFunc.X, (mem_fixedField_iff _ _).mpr <| by
    rintro _ ⟨σ, rfl⟩
    rw [semilinearAction_algebraMap_ratFunc, RatFunc.mapRingEquiv_X]⟩

private theorem transcendental_gen : Transcendental K D.gen := by
  have ht : Transcendental L (algebraMap (RatFunc L) X RatFunc.X) :=
    (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective (RatFunc L) X)).mpr
      RatFunc.transcendental_X
  exact (transcendental_algebraMap_iff
    (algebraMap (fixedField D.semilinearAction.range) X).injective).mp (ht.of_tower_top K)

/-- With `t` acting as itself, the Belyi function of `X` is the image of the variable of `K(t)`. -/
private theorem algebraMap_gen :
    letI := ratFuncAlgebraOfTranscendental D.transcendental_gen
    algebraMap (fixedField D.semilinearAction.range) X (algebraMap (RatFunc K) _ RatFunc.X) =
      algebraMap (RatFunc L) X RatFunc.X := by
  let := ratFuncAlgebraOfTranscendental D.transcendental_gen
  rw [algebraMap_ratFuncAlgebraOfTranscendental_X]
  rfl

variable [CharZero K] [FiniteDimensional K L] [IsGalois K L]

/-- The **descended Belyi pair** of a descent datum: the fixed field `F₀` of its semilinear action
on the function field `F` of `X`, over `K(t)` through the Belyi function `t` of `X`, which lies in
`F₀`. It is an algebraic Belyi pair over `K` whose base change to `L` is `X`
(`TauCeti.AlgebraicBelyiPair.DescentDatum.constantCompositum_descend_eq_top`,
`TauCeti.AlgebraicBelyiPair.DescentDatum.baseChangeEquiv`). -/
noncomputable def descend : AlgebraicBelyiPair K :=
  letI := ratFuncAlgebraOfTranscendental D.transcendental_gen
  haveI := isScalarTower_ratFuncAlgebraOfTranscendental D.transcendental_gen
  haveI := GaloisDescent.finiteDimensional_ratFunc_fixedField D.semilinearAction_algebraMap
    X.isAlgebraicBelyiPair.isIntegrallyClosedIn D.algebraMap_gen
  { carrier := fixedField D.semilinearAction.range
    isAlgebraicBelyiPair := (GaloisDescent.isAlgebraicBelyiPair_fixedField_iff
      D.semilinearAction_algebraMap D.algebraMap_gen).mpr X.isAlgebraicBelyiPair }

/-- The function field of the descended pair embeds in that of `X`, as the fixed field of the
semilinear action. -/
noncomputable instance : Algebra D.descend X :=
  inferInstanceAs (Algebra (fixedField D.semilinearAction.range) X)

instance : IsScalarTower K D.descend X :=
  inferInstanceAs (IsScalarTower K (fixedField D.semilinearAction.range) X)

/-- The function field of the descended pair is the field of elements of the function field of
`X` fixed by the semilinear action. -/
theorem mem_range_algebraMap_descend_iff {x : X} :
    x ∈ Set.range (algebraMap D.descend X) ↔ ∀ σ, D.semilinearAction σ x = x := by
  refine ⟨?_, fun h ↦ ⟨⟨x, (mem_fixedField_iff _ _).mpr ?_⟩, rfl⟩⟩
  · rintro ⟨y, rfl⟩ σ
    exact (mem_fixedField_iff _ _).mp y.2 _ ⟨σ, rfl⟩
  · rintro _ ⟨σ, rfl⟩
    exact h σ

/-- The semilinear action of a descent datum fixes the function field of the descended pair. -/
@[simp]
theorem semilinearAction_algebraMap_descend (σ : L ≃ₐ[K] L) (y : D.descend) :
    D.semilinearAction σ (algebraMap D.descend X y) = algebraMap D.descend X y :=
  D.mem_range_algebraMap_descend_iff.mp ⟨y, rfl⟩ σ

/-- **The Belyi function descends**: the Belyi function of the descended pair is that of `X`. -/
@[simp]
theorem algebraMap_descend_X :
    algebraMap D.descend X (algebraMap (RatFunc K) D.descend RatFunc.X) =
      algebraMap (RatFunc L) X RatFunc.X :=
  D.algebraMap_gen

/-- **The descended pair base-changes back**: the function field of `X` is the compositum of that
of the descended pair with `L`. -/
theorem constantCompositum_descend_eq_top : constantCompositum D.descend L X = ⊤ :=
  GaloisDescent.constantCompositum_fixedField_eq_top D.semilinearAction_algebraMap

/-- The descended pair has the degree of `X`. -/
@[simp]
theorem finrank_descend :
    Module.finrank (RatFunc K) D.descend = Module.finrank (RatFunc L) X := by
  let := ratFuncAlgebraOfTranscendental D.transcendental_gen
  have := isScalarTower_ratFuncAlgebraOfTranscendental D.transcendental_gen
  -- Elaborated without the expected type, whose instances are the fields of `descend`.
  have h := GaloisDescent.finrank_ratFunc_fixedField D.semilinearAction_algebraMap
    X.isAlgebraicBelyiPair.isIntegrallyClosedIn D.algebraMap_gen
  exact h

/-- The **base-change isomorphism** of a descent datum: extending the scalars of the function field
of the descended pair from `K` to `L` recovers the function field of `X`, by `a ⊗ y ↦ a • y`. -/
noncomputable def baseChangeEquiv : L ⊗[K] D.descend ≃ₐ[L] X :=
  GaloisDescent.fixedFieldBaseChangeEquiv D.semilinearAction_algebraMap

@[simp]
theorem baseChangeEquiv_tmul (a : L) (y : D.descend) :
    D.baseChangeEquiv (a ⊗ₜ y) = a • algebraMap D.descend X y :=
  GaloisDescent.fixedFieldBaseChangeEquiv_tmul D.semilinearAction_algebraMap a y

@[simp]
theorem baseChangeEquiv_symm_algebraMap (y : D.descend) :
    D.baseChangeEquiv.symm (algebraMap D.descend X y) = 1 ⊗ₜ y :=
  GaloisDescent.fixedFieldBaseChangeEquiv_symm_apply_coe D.semilinearAction_algebraMap y

/-- **A descent datum gives a model**: the descended pair, embedded in the function field of `X`
as the fixed field of the semilinear action, is a model of `X` over `K`. -/
@[expose, simps pair embedding]
noncomputable def model : Model K X where
  pair := D.descend
  embedding := algebraMap D.descend X
  embedding_algebraMap c := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K L X]
  embedding_algebraMap_X := D.algebraMap_descend_X
  adjoin_range_embedding := by
    have h := D.constantCompositum_descend_eq_top
    rw [← IntermediateField.toSubfield_inj, IntermediateField.top_toSubfield,
      constantCompositum_def, IntermediateField.adjoin_toSubfield] at h
    rw [← IntermediateField.toSubfield_inj, IntermediateField.top_toSubfield,
      IntermediateField.adjoin_toSubfield, Set.union_comm, h]

include D in
/-- **Descent data are effective**: an algebraic Belyi pair with a descent datum relative to `K`
is defined over `K`. -/
theorem isDefinedOver_mk : (IsoClass.mk X).IsDefinedOver K :=
  IsoClass.isDefinedOver_mk_iff.mpr ⟨D.model⟩

end DescentDatum

end AlgebraicBelyiPair

end TauCeti
