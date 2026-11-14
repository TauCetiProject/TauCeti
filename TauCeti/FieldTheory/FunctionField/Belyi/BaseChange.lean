/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Bundled
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic
public import TauCeti.RingTheory.TensorProduct.FractionRing
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basis
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Degree
import TauCeti.FieldTheory.FunctionField.ConstantExtension.FractionField
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Parameter
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Place
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Ramification
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Regular
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.FieldTheory.FunctionField.SeparablyGenerated
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Base change of algebraic Belyi pairs

Let `F / k(t)` be a function field over the rational function field over a field `k` of
characteristic zero, and let `k' / k` be an arbitrary field extension, algebraic or transcendental.
The **base change** of `F` to `k'` is the compositum `F' = F · k'`,
regarded as a field over `k'(t)` through the same function `t`. When `k` is the exact constant
field of `F`, it is the function field of the base change of the curve of `F` to `k'`, with the
base change of the map to the projective line.

This file shows that `F'` is an algebraic Belyi pair over `k'` exactly when `F` is one over `k`,
provided `k` is the exact constant field of `F`
(`TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`), and descends Belyi pairs under
degree equality (`TauCeti.isAlgebraicBelyiPair_of_finrank_eq`). Its degree is unchanged
(`TauCeti.finrank_ratFunc_eq_of_isGeometricallyReduced`), and `F'` is finite over `k'(t)` as
soon as `F` is finite over `k(t)`
(`TauCeti.finiteDimensional_ratFunc_of_constantCompositum_eq_top`).

For bundled pairs we construct `TauCeti.AlgebraicBelyiPair.baseChange` with carrier
`FractionRing (X ⊗[k] k')`, and prove full faithfulness on isomorphisms and injectivity on
`IsoClass` when `k` is algebraically closed (`AlgebraicBelyiPair.IsoClass.baseChange_injective`).

## Main results

* `TauCeti.Place.restrict_restrict_eq_markedPlace_iff`: base change matches the places over each
  marked place.
* `TauCeti.Place.restrict_restrict_mem_zeroOneInfty_iff`: base change matches the places over the
  marked places.
* `TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`: the base change of `F` to `k'`
  is an algebraic Belyi pair exactly when `F` is.
* `TauCeti.AlgebraicBelyiPair.baseChange` and
  `TauCeti.AlgebraicBelyiPair.IsoClass.baseChange_injective`: bundled base change.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6.
* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265.
-/

public section

open Polynomial
open scoped TensorProduct IntermediateField

namespace TauCeti

section Unbundled

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']

namespace Place

variable [Algebra.IsIntegral (RatFunc k) F] [Algebra.IsIntegral (RatFunc k') F']

/-- Under base change, a function of `k(t)` and one of `k'(t)` with the same image in `F'` have a
zero at the places below `Q'` together, because all the ramification indices are positive. -/
private theorem ord_restrict_restrict_pos_iff [Algebra.IsIntegral F F'] (Q' : Place k' F')
    {f : RatFunc k} {f' : RatFunc k'}
    (h : algebraMap F F' (algebraMap (RatFunc k) F f) = algebraMap (RatFunc k') F' f') :
    0 < ((Q'.restrict k F).restrict k (RatFunc k)).ord f ↔
      0 < (Q'.restrict k' (RatFunc k')).ord f' := by
  rw [← ord_algebraMap_pos_iff k' (RatFunc k') Q', ← h, ord_algebraMap_pos_iff k F Q',
    ord_algebraMap_pos_iff k (RatFunc k)]

/-- **Base change keeps each marked fibre**: if `t` acts on `F'` as it does on `F`, then a place
`Q'` of `F'` lies over the marked place of `k'(t)` numbered `i` exactly when the place of `F` below
it lies over the marked place of `k(t)` numbered `i`. -/
theorem restrict_restrict_eq_markedPlace_iff [Algebra.IsIntegral F F']
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (Q' : Place k' F') (i : Fin 3) :
    (Q'.restrict k F).restrict k (RatFunc k) = markedPlace k i ↔
      Q'.restrict k' (RatFunc k') = markedPlace k' i := by
  fin_cases i
  · simp only [Fin.zero_eta, markedPlace_zero, ← ord_X_pos_iff]
    exact ord_restrict_restrict_pos_iff Q' hX
  · simp only [Fin.mk_one, markedPlace_one, ← ord_X_sub_C_pos_iff]
    exact ord_restrict_restrict_pos_iff Q' (by simp only [map_one, map_sub, hX])
  · simp only [Fin.reduceFinMk, markedPlace_two, ← X_notMem_integers_iff_eq_infty]
    rw [mem_integers_restrict_iff k (RatFunc k), mem_integers_restrict_iff k F,
      mem_integers_restrict_iff k' (RatFunc k'), hX]

/-- **Base change matches the marked places**: if `t` acts on `F'` as it does on `F`, then a
place `Q'` of `F'` lies over one of the marked places `t = 0`, `t = 1`, `t = ∞` of `k'(t)` exactly
when the place of `F` below it lies over one of those of `k(t)`. -/
theorem restrict_restrict_mem_zeroOneInfty_iff [Algebra.IsIntegral F F']
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (Q' : Place k' F') :
    (Q'.restrict k F).restrict k (RatFunc k) ∈ zeroOneInfty k ↔
      Q'.restrict k' (RatFunc k') ∈ zeroOneInfty k' := by
  simp only [← range_markedPlace, Set.mem_range, eq_comm (b := Place.restrict _ _ _),
    restrict_restrict_eq_markedPlace_iff hX]

omit [Algebra.IsIntegral (RatFunc k) F] in
/-- **A vertical place never lies over `0`, `1` or `∞`**. -/
theorem restrict_notMem_zeroOneInfty_of_isTrivialOn
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q' : Place k' F'}
    (hQ' : Q'.valuation.IsTrivialOn F) :
    Q'.restrict k' (RatFunc k') ∉ zeroOneInfty k' := by
  rw [notMem_zeroOneInfty_iff]
  exact ⟨by simpa using ord_restrict_algebraMap_eq_zero_of_isTrivialOn hX hQ' X_ne_zero, by
    simpa [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] using
      ord_restrict_algebraMap_eq_zero_of_isTrivialOn hX hQ' (X_sub_C_ne_zero (1 : k))⟩

omit [Algebra k k'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
private theorem ord_restrict_pos_iff_of_integers_comap_eq {Q : Place k F} {Q' : Place k' F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) {f : RatFunc k} {f' : RatFunc k'}
    (h : algebraMap F F' (algebraMap (RatFunc k) F f) = algebraMap (RatFunc k') F' f') :
    0 < (Q.restrict k (RatFunc k)).ord f ↔ 0 < (Q'.restrict k' (RatFunc k')).ord f' := by
  obtain ⟨he_pos, hord⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ'
  rw [← ord_algebraMap_pos_iff k (RatFunc k) Q, ← ord_algebraMap_pos_iff k' (RatFunc k') Q', ← h,
    hord, mul_pos_iff_of_pos_left (by exact_mod_cast he_pos)]

omit [Algebra k k'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- **Contracting places preserve each marked fibre across arbitrary constant extensions.** -/
theorem restrict_eq_markedPlace_iff_of_integers_comap_eq
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q : Place k F} {Q' : Place k' F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) (i : Fin 3) :
    Q.restrict k (RatFunc k) = markedPlace k i ↔
      Q'.restrict k' (RatFunc k') = markedPlace k' i := by
  fin_cases i
  · simp only [Fin.zero_eta, markedPlace_zero, ← ord_X_pos_iff]
    exact ord_restrict_pos_iff_of_integers_comap_eq hQ' hX
  · simp only [Fin.mk_one, markedPlace_one, ← ord_X_sub_C_pos_iff]
    exact ord_restrict_pos_iff_of_integers_comap_eq hQ' (by simp only [map_one, map_sub, hX])
  · simp only [Fin.reduceFinMk, markedPlace_two, ← X_notMem_integers_iff_eq_infty]
    rw [mem_integers_restrict_iff k (RatFunc k), ← hQ', ValuationSubring.mem_comap, hX,
      mem_integers_restrict_iff k' (RatFunc k')]

omit [Algebra k k'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- **Contracting places match `{0, 1, ∞}` across arbitrary constant extensions.** -/
theorem restrict_mem_zeroOneInfty_iff_of_integers_comap_eq
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q : Place k F} {Q' : Place k' F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) :
    Q.restrict k (RatFunc k) ∈ zeroOneInfty k ↔
      Q'.restrict k' (RatFunc k') ∈ zeroOneInfty k' := by
  simp only [← range_markedPlace, Set.mem_range, eq_comm (b := Place.restrict _ _ _),
    restrict_eq_markedPlace_iff_of_integers_comap_eq hX hQ']

end Place

variable [CharZero k] [FiniteDimensional (RatFunc k) F] [FiniteDimensional (RatFunc k') F']

omit [Field k'] [Field F'] [Algebra k k'] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra (RatFunc k') F']
  [IsScalarTower k' (RatFunc k') F'] [FiniteDimensional (RatFunc k') F'] in
private theorem isGeometricallyReduced_ratFunc_charZero : Algebra.IsGeometricallyReduced k F :=
  have hF : IsFunctionField k F := (IsFunctionField.ratFunc k).finite_extension
  let ⟨_, hx₀, _⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  isGeometricallyReduced_of_separating hx₀

open Place in
/-- **Base change of algebraic Belyi pairs**: let `F / k(t)` have exact constant field `k`, of
characteristic zero, and let `F' = F · k'` be its compositum with any field extension `k' / k`,
with `t` acting on `F'` as it does on `F`. Then `F' / k'(t)` is an algebraic Belyi pair exactly
when `F / k(t)` is. -/
theorem isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top [CharZero k']
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) :
    IsAlgebraicBelyiPair k' F' ↔ IsAlgebraicBelyiPair k F := by
  have hF : IsFunctionField k F := (IsFunctionField.ratFunc k).finite_extension
  have : Algebra.IsGeometricallyReduced k F := isGeometricallyReduced_ratFunc_charZero
  have H := linearDisjoint_of_isGeometricallyReduced_ratFunc hex hX
  refine ⟨fun h' ↦ ⟨hex, fun {Q} hQ ↦ ?_⟩,
    fun h ↦ ⟨hex.of_constantCompositum_eq_top_of_linearDisjoint H hcomp, fun {Q'} hQ' ↦ ?_⟩⟩
  · obtain ⟨Q', hQ'⟩ := exists_integers_comap_eq hF H hcomp Q
    rw [← ramificationIdx_ratFunc_eq_of_integers_comap_eq hex hcomp hX hQ']
    exact h'.ramificationIdx_eq_one
      ((restrict_mem_zeroOneInfty_iff_of_integers_comap_eq hX hQ').not.mp hQ)
  · rcases isTrivialOn_or_existsUnique_integers_comap_eq hF Q' with htriv | ⟨Q, hQ, -⟩
    · exact ramificationIdx_ratFunc_eq_one_of_isTrivialOn hcomp hX htriv
    · rw [ramificationIdx_ratFunc_eq_of_integers_comap_eq hex hcomp hX hQ]
      exact h.ramificationIdx_eq_one
        ((restrict_mem_zeroOneInfty_iff_of_integers_comap_eq hX hQ).not.mpr hQ')

/-- **Degree-preserving descent of an algebraic Belyi pair** across an arbitrary extension. -/
theorem isAlgebraicBelyiPair_of_finrank_eq [CharZero k'] (h' : IsAlgebraicBelyiPair k' F')
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    (hfin : Module.finrank (RatFunc k) F = Module.finrank (RatFunc k') F') :
    IsAlgebraicBelyiPair k F :=
  have H := linearDisjoint_of_finrank_ratFunc_eq hcomp hX hfin.symm
  (isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top
    (isIntegrallyClosedIn_of_linearDisjoint H h'.isIntegrallyClosedIn) hcomp hX).mp h'

end Unbundled

namespace AlgebraicBelyiPair

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

universe u

variable {k : Type u} [Field k] [CharZero k]

/-- For an algebraic Belyi pair `X` over `k` and any extension `k' / k`, `X ⊗[k] k'` is a domain. -/
theorem isDomain_tensorProduct (k' : Type*) [Field k'] [Algebra k k'] (X : AlgebraicBelyiPair k) :
    IsDomain (X ⊗[k] k') :=
  have := isGeometricallyReduced_ratFunc_charZero (k := k) (F := X)
  isDomain_tensorProduct_of_isGeometricallyReduced X.isAlgebraicBelyiPair.isIntegrallyClosedIn k'

section BaseChange

variable (k' : Type u) [Field k'] [CharZero k'] [Algebra k k']

omit [CharZero k'] in
private theorem transcendental_baseChange_X (X : AlgebraicBelyiPair k) :
    letI := X.isDomain_tensorProduct k'
    Transcendental k'
      (algebraMap X (FractionRing (X ⊗[k] k')) (algebraMap (RatFunc k) X RatFunc.X)) :=
  letI := X.isDomain_tensorProduct k'
  (linearDisjoint_of_isFractionRing_tensorProduct (k := k)).transcendental_algebraMap <|
    (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective (RatFunc k) X)).mpr
      RatFunc.transcendental_X

/-- **Base change of a bundled algebraic Belyi pair** along a field extension `k → k'`. -/
noncomputable def baseChange (X : AlgebraicBelyiPair k) : AlgebraicBelyiPair k' :=
  letI := X.isDomain_tensorProduct k'
  let tx := transcendental_baseChange_X k' X
  letI := ratFuncAlgebraOfTranscendental tx
  haveI := isScalarTower_ratFuncAlgebraOfTranscendental tx
  have hcomp : constantCompositum X k' (FractionRing (X ⊗[k] k')) = ⊤ := by
    rw [constantCompositum_def]
    exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k)
  have hX : algebraMap X (FractionRing (X ⊗[k] k')) (algebraMap (RatFunc k) X RatFunc.X) =
      algebraMap (RatFunc k') (FractionRing (X ⊗[k] k')) RatFunc.X :=
    (algebraMap_ratFuncAlgebraOfTranscendental_X tx).symm
  haveI := finiteDimensional_ratFunc_of_constantCompositum_eq_top hcomp hX
  { carrier := FractionRing (X ⊗[k] k')
    isAlgebraicBelyiPair := (isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top
      X.isAlgebraicBelyiPair.isIntegrallyClosedIn hcomp hX).mpr X.isAlgebraicBelyiPair }

noncomputable instance (X : AlgebraicBelyiPair k) : Algebra k (X.baseChange k') :=
  ((algebraMap k' (X.baseChange k')).comp (algebraMap k k')).toAlgebra

instance (X : AlgebraicBelyiPair k) : IsScalarTower k k' (X.baseChange k') := .of_algebraMap_eq' rfl

/-- The canonical `k`-algebra embedding `X →ₐ[k] X.baseChange k'` into the base change. -/
noncomputable def toBaseChange (X : AlgebraicBelyiPair k) : X →ₐ[k] X.baseChange k' :=
  letI := X.isDomain_tensorProduct k'
  { algebraMap X (FractionRing (X ⊗[k] k')) with
    commutes' := fun c ↦ by
      change algebraMap X (FractionRing (X ⊗[k] k')) (algebraMap k X c) =
        algebraMap k' (FractionRing (X ⊗[k] k')) (algebraMap k k' c)
      rw [← IsScalarTower.algebraMap_apply k X, ← IsScalarTower.algebraMap_apply k k'] }

@[simp] theorem toBaseChange_algebraMap_X (X : AlgebraicBelyiPair k) :
    X.toBaseChange k' (algebraMap (RatFunc k) X RatFunc.X) =
      algebraMap (RatFunc k') (X.baseChange k') RatFunc.X :=
  letI := X.isDomain_tensorProduct k'
  (algebraMap_ratFuncAlgebraOfTranscendental_X (transcendental_baseChange_X k' X)).symm

noncomputable instance (X : AlgebraicBelyiPair k) : Algebra X (X.baseChange k') :=
  (X.toBaseChange k').toRingHom.toAlgebra

instance (X : AlgebraicBelyiPair k) : IsScalarTower k X (X.baseChange k') :=
  .of_algebraMap_eq fun c ↦ ((X.toBaseChange k').commutes c).symm

@[simp] theorem algebraMap_baseChange_X (X : AlgebraicBelyiPair k) :
    algebraMap X (X.baseChange k') (algebraMap (RatFunc k) X RatFunc.X) =
      algebraMap (RatFunc k') (X.baseChange k') RatFunc.X :=
  X.toBaseChange_algebraMap_X k'

/-- Linear disjointness of `X` and `k'` inside `X.baseChange k'`. -/
theorem linearDisjoint_baseChange (X : AlgebraicBelyiPair k) :
    (IsScalarTower.toAlgHom k k' (X.baseChange k')).fieldRange.LinearDisjoint X := by
  let _ := X.isDomain_tensorProduct k'
  have hinj := productMap_injective_iff_linearDisjoint.mpr
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k)
      (Q := FractionRing (X ⊗[k] k')) (F := X) (K := k'))
  refine productMap_injective_iff_linearDisjoint.mp fun u v huv ↦ ?_
  have heq (z : X ⊗[k] k') :
      Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k X (X.baseChange k'))
        (IsScalarTower.toAlgHom k k' (X.baseChange k')) z =
      Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k X (FractionRing (X ⊗[k] k')))
        (IsScalarTower.toAlgHom k k' (FractionRing (X ⊗[k] k'))) z := by
    induction z using TensorProduct.inductionOn with
    | tmul _ _ => rfl
    | add _ _ hu hv => rw [map_add, map_add, hu, hv]; rfl
  exact hinj ((heq u).symm.trans (huv.trans (heq v)))

/-- `X` and `k'` generate `X.baseChange k'` as a field. -/
theorem constantCompositum_baseChange_eq_top (X : AlgebraicBelyiPair k) :
    constantCompositum X k' (X.baseChange k') = ⊤ := by
  let _ := X.isDomain_tensorProduct k'
  have h2 : constantCompositum X k' (FractionRing (X ⊗[k] k')) = ⊤ := by
    rw [constantCompositum_def]
    exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k)
  rw [← IntermediateField.toSubfield_inj, IntermediateField.top_toSubfield, constantCompositum_def,
    IntermediateField.adjoin_toSubfield] at h2 ⊢; exact h2

@[simp] theorem finrank_baseChange (X : AlgebraicBelyiPair k) :
    Module.finrank (RatFunc k') (X.baseChange k') = Module.finrank (RatFunc k) X :=
  have := isGeometricallyReduced_ratFunc_charZero (k := k) (F := X)
  finrank_ratFunc_eq_of_isGeometricallyReduced X.isAlgebraicBelyiPair.isIntegrallyClosedIn
    (X.constantCompositum_baseChange_eq_top k') (X.algebraMap_baseChange_X k')

variable {k'}

/-- Functoriality of `baseChange` on isomorphisms of algebraic Belyi pairs. -/
noncomputable def baseChangeAlgEquiv {X Y : AlgebraicBelyiPair k} (e : X ≃ₐ[RatFunc k] Y) :
    X.baseChange k' ≃ₐ[RatFunc k'] Y.baseChange k' :=
  ratFuncConstantExtensionAlgEquiv (X.linearDisjoint_baseChange k')
    (X.constantCompositum_baseChange_eq_top k') (Y.linearDisjoint_baseChange k')
    (Y.constantCompositum_baseChange_eq_top k') (X.algebraMap_baseChange_X k')
    (Y.algebraMap_baseChange_X k') e

variable (k') in
/-- Full faithfulness of `baseChange` on Belyi pair isomorphisms over algebraically closed `k`. -/
noncomputable def baseChangeAlgEquivEquiv [IsAlgClosed k] (X Y : AlgebraicBelyiPair k) :
    (X ≃ₐ[RatFunc k] Y) ≃ (X.baseChange k' ≃ₐ[RatFunc k'] Y.baseChange k') :=
  ratFuncConstantExtensionAlgEquivEquiv (X.linearDisjoint_baseChange k')
    (X.constantCompositum_baseChange_eq_top k') (Y.linearDisjoint_baseChange k')
    (Y.constantCompositum_baseChange_eq_top k') (X.algebraMap_baseChange_X k')
    (Y.algebraMap_baseChange_X k')

namespace IsoClass

variable (k') in
/-- **Base change of isomorphism classes of algebraic Belyi pairs** along `k → k'`. -/
noncomputable def baseChange : IsoClass k → IsoClass k' :=
  lift (fun X ↦ mk (X.baseChange k')) fun _ _ e ↦ mk_eq_mk (baseChangeAlgEquiv e)

@[simp] theorem baseChange_mk (X : AlgebraicBelyiPair k) :
    (mk X).baseChange k' = mk (X.baseChange k') := lift_mk _ _ X

@[simp] theorem degree_baseChange (c : IsoClass k) : (c.baseChange k').degree = c.degree := by
  induction c using ind with | h X => simp [finrank_baseChange]

/-- **Base change of isomorphism classes from an algebraically closed field is injective.** -/
theorem baseChange_injective [IsAlgClosed k] : Function.Injective (baseChange (k := k) k') := by
  intro c₁ c₂
  induction c₁ using ind with | h X => ?_
  induction c₂ using ind with | h Y => ?_
  simp only [baseChange_mk, mk_eq_mk_iff]
  exact fun ⟨e'⟩ ↦ ⟨(baseChangeAlgEquivEquiv k' X Y).symm e'⟩

@[simp] theorem baseChange_eq_iff [IsAlgClosed k] {c₁ c₂ : IsoClass k} :
    c₁.baseChange k' = c₂.baseChange k' ↔ c₁ = c₂ :=
  (baseChange_injective (k := k) (k' := k')).eq_iff

end IsoClass

end BaseChange

end AlgebraicBelyiPair

end TauCeti
