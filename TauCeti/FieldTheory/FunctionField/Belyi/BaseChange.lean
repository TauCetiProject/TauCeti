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
characteristic zero, and let `k' / k` be an arbitrary field extension, algebraic or transcendental
(for instance `AlgebraicClosure ℚ ⊂ ℂ` or a subfield `K ⊂ ℂ` fixed by a subgroup of `Aut(ℂ)`). The
**base change** of `F` to `k'` is the compositum `F' = F · k'`, realized concretely as
`FractionRing (F ⊗[k] k')`, regarded as a field over `k'(t)` through the same function `t`.

This file shows that `F'` is an algebraic Belyi pair over `k'` if and only if `F` is one over `k`,
provided `k` is the exact constant field of `F`
(`TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`), with no algebraicity assumption
on `k' / k`. When `F' / k'(t)` is already an algebraic Belyi pair and `[F : k(t)] = [F' : k'(t)]`,
linear disjointness descends exactness of constants automatically, so `F / k(t)` is an algebraic
Belyi pair (`TauCeti.isAlgebraicBelyiPair_of_finrank_eq`).

For an arbitrary constant extension `k ⊂ k'`, a place `Q'` of `F'` either is trivial on `F` — a
vertical place moving with transcendental parameters in `k'`, which never lies over `0`, `1` or
`∞` (`TauCeti.Place.restrict_notMem_zeroOneInfty_of_isTrivialOn`) and is unramified over `k'(t)`
(`TauCeti.Place.ramificationIdx_ratFunc_eq_one_of_isTrivialOn`) — or contracts to a unique place
`Q` of `F` with the same ramification index over the line and the same marked-place incidences
(`TauCeti.Place.restrict_eq_markedPlace_iff_of_integers_comap_eq`). Conversely, every place `Q` of
`F` extends to a place `Q'` of `F'` contracting to it (`TauCeti.Place.exists_integers_comap_eq`).

For bundled pairs we construct `TauCeti.AlgebraicBelyiPair.baseChange`, preserving the degree, and
when `k` is algebraically closed we show that base change is fully faithful on `k(t)`-isomorphisms
(`TauCeti.AlgebraicBelyiPair.baseChangeAlgEquivEquiv`) and injective on isomorphism classes
(`TauCeti.AlgebraicBelyiPair.IsoClass.baseChange_injective`).

## Main definitions

* `TauCeti.AlgebraicBelyiPair.baseChange`: base change of a bundled algebraic Belyi pair along an
  arbitrary field extension `k → k'`, with carrier `FractionRing (X ⊗[k] k')`.
* `TauCeti.AlgebraicBelyiPair.baseChangeAlgEquivEquiv`: over an algebraically closed base field `k`,
  the equivalence `(X ≃ₐ[RatFunc k] Y) ≃ (X.baseChange k' ≃ₐ[RatFunc k'] Y.baseChange k')`.
* `TauCeti.AlgebraicBelyiPair.IsoClass.baseChange`: base change of isomorphism classes of algebraic
  Belyi pairs.

## Main results

* `TauCeti.Place.restrict_notMem_zeroOneInfty_of_isTrivialOn`: a place of `F'` trivial on `F` does
  not lie over `0`, `1` or `∞`.
* `TauCeti.Place.restrict_eq_markedPlace_iff_of_integers_comap_eq` and
  `TauCeti.Place.restrict_mem_zeroOneInfty_iff_of_integers_comap_eq`: marked-place incidences match
  across any constant extension at contracting places.
* `TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`: `F · k'` is an algebraic Belyi
  pair over `k'` if and only if `F` is one over `k`, for arbitrary `k' / k`.
* `TauCeti.isAlgebraicBelyiPair_of_finrank_eq`: degree-preserving coefficient descent of an
  algebraic Belyi pair along an arbitrary extension `k ⊂ k'`.
* `TauCeti.AlgebraicBelyiPair.IsoClass.baseChange_injective`: base change of isomorphism classes
  from an algebraically closed field is injective.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6.
* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  Section 2.
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

section Integral

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
`Q'` of `F'` integral over `F` lies over the marked place of `k'(t)` numbered `i` exactly when the
place of `F` below it lies over the marked place of `k(t)` numbered `i`. -/
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
place `Q'` of `F'` integral over `F` lies over one of the marked places `t = 0`, `t = 1`, `t = ∞` of
`k'(t)` exactly when the place of `F` below it lies over one of those of `k(t)`. -/
theorem restrict_restrict_mem_zeroOneInfty_iff [Algebra.IsIntegral F F']
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (Q' : Place k' F') :
    (Q'.restrict k F).restrict k (RatFunc k) ∈ zeroOneInfty k ↔
      Q'.restrict k' (RatFunc k') ∈ zeroOneInfty k' := by
  simp only [← range_markedPlace, Set.mem_range, eq_comm (b := Place.restrict _ _ _),
    restrict_restrict_eq_markedPlace_iff hX]

end Integral

/-- **A vertical place never lies over `0`, `1` or `∞`**: if `Q'` is trivial on `F` and `t` acts on
`F'` as it does on `F`, then both `t` and `t - 1` have order zero below `Q'`. -/
theorem restrict_notMem_zeroOneInfty_of_isTrivialOn [Algebra.IsIntegral (RatFunc k') F']
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q' : Place k' F'}
    (hQ' : Q'.valuation.IsTrivialOn F) :
    Q'.restrict k' (RatFunc k') ∉ zeroOneInfty k' := by
  rw [notMem_zeroOneInfty_iff]
  refine ⟨?_, ?_⟩
  · simpa using ord_restrict_algebraMap_eq_zero_of_isTrivialOn hX hQ' X_ne_zero
  · have h := ord_restrict_algebraMap_eq_zero_of_isTrivialOn hX hQ' (X_sub_C_ne_zero (1 : k))
    simpa [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] using h

omit [Algebra k k'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- Under any contraction of valuation rings `Q'.integers.comap (algebraMap F F') = Q.integers`, a
function of `k(t)` and one of `k'(t)` with the same image in `F'` have positive order at the places
below `Q` and `Q'` together, because all ramification indices are positive. -/
private theorem ord_restrict_pos_iff_of_integers_comap_eq
    [Algebra.IsIntegral (RatFunc k) F] [Algebra.IsIntegral (RatFunc k') F']
    {Q : Place k F} {Q' : Place k' F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers)
    {f : RatFunc k} {f' : RatFunc k'}
    (h : algebraMap F F' (algebraMap (RatFunc k) F f) = algebraMap (RatFunc k') F' f') :
    0 < (Q.restrict k (RatFunc k)).ord f ↔ 0 < (Q'.restrict k' (RatFunc k')).ord f' := by
  obtain ⟨he_pos, hord⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ'
  rw [← ord_algebraMap_pos_iff k (RatFunc k) Q, ← ord_algebraMap_pos_iff k' (RatFunc k') Q', ← h,
    hord, mul_pos_iff_of_pos_left (by exact_mod_cast he_pos)]

omit [Algebra k k'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- **Contracting places preserve each marked fibre across arbitrary constant extensions**: if `Q'`
contracts to `Q` and `t` acts compatibly on `F` and `F'`, then `Q` lies over the `i`-th marked
place of `k(t)` if and only if `Q'` lies over the `i`-th marked place of `k'(t)`. -/
theorem restrict_eq_markedPlace_iff_of_integers_comap_eq
    [Algebra.IsIntegral (RatFunc k) F] [Algebra.IsIntegral (RatFunc k') F']
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {Q : Place k F} {Q' : Place k' F'}
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
/-- **Contracting places match the marked set `{0, 1, ∞}` across arbitrary constant extensions.** -/
theorem restrict_mem_zeroOneInfty_iff_of_integers_comap_eq
    [Algebra.IsIntegral (RatFunc k) F] [Algebra.IsIntegral (RatFunc k') F']
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {Q : Place k F} {Q' : Place k' F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) :
    Q.restrict k (RatFunc k) ∈ zeroOneInfty k ↔
      Q'.restrict k' (RatFunc k') ∈ zeroOneInfty k' := by
  simp only [← range_markedPlace, Set.mem_range, eq_comm (b := Place.restrict _ _ _),
    restrict_eq_markedPlace_iff_of_integers_comap_eq hX hQ']

end Place

section ArbitraryBaseChange

variable [CharZero k] [FiniteDimensional (RatFunc k) F] [FiniteDimensional (RatFunc k') F']

open Place in
/-- **Base change of algebraic Belyi pairs along an arbitrary constant extension**: let `F / k(t)`
have exact constant field `k`, of characteristic zero, and let `F' = F · k'` be its compositum with
any field extension `k' / k` (algebraic or transcendental), with `t` acting on `F'` as it does on
`F`. Then `F' / k'(t)` is an algebraic Belyi pair if and only if `F / k(t)` is. -/
theorem isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top [CharZero k']
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) :
    IsAlgebraicBelyiPair k' F' ↔ IsAlgebraicBelyiPair k F := by
  have hF : IsFunctionField k F := (IsFunctionField.ratFunc k).finite_extension
  obtain ⟨x₀, hx₀, _⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  have : Algebra.IsGeometricallyReduced k F := isGeometricallyReduced_of_separating hx₀
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

/-- **Degree-preserving descent of an algebraic Belyi pair**: if `F' = F · k'` is an algebraic Belyi
pair over `k'` (with `k' / k` possibly transcendental), `t` acts on `F'` as on `F`, and
`[F : k(t)] = [F' : k'(t)]`, then `k` is automatically exact in `F` and `F / k(t)` is an algebraic
Belyi pair. -/
theorem isAlgebraicBelyiPair_of_finrank_eq [CharZero k'] (h' : IsAlgebraicBelyiPair k' F')
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    (hfin : Module.finrank (RatFunc k) F = Module.finrank (RatFunc k') F') :
    IsAlgebraicBelyiPair k F := by
  have H := linearDisjoint_of_finrank_ratFunc_eq hcomp hX hfin.symm
  have hex := isIntegrallyClosedIn_of_linearDisjoint H h'.isIntegrallyClosedIn
  exact (isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top hex hcomp hX).mp h'

end ArbitraryBaseChange

end Unbundled

/-! ### Base change of bundled algebraic Belyi pairs -/

namespace AlgebraicBelyiPair

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

universe u

variable {k : Type u} [Field k] [CharZero k]

/-- For an algebraic Belyi pair `X` over `k` and any field extension `k' / k`, `X ⊗[k] k'` is an
integral domain because `k` is of characteristic zero and exact in `X`. -/
theorem isDomain_tensorProduct (k' : Type*) [Field k'] [Algebra k k'] (X : AlgebraicBelyiPair k) :
    IsDomain (X ⊗[k] k') := by
  have hF : IsFunctionField k X := (IsFunctionField.ratFunc k).finite_extension
  obtain ⟨x₀, hx₀, _⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  have : Algebra.IsGeometricallyReduced k X := isGeometricallyReduced_of_separating hx₀
  exact isDomain_tensorProduct_of_isGeometricallyReduced
    X.isAlgebraicBelyiPair.isIntegrallyClosedIn k'

section BaseChange

variable (k' : Type u) [Field k'] [CharZero k'] [Algebra k k']

omit [CharZero k'] in
/-- Auxiliary transcendence proof for the image of `t` in `FractionRing (X ⊗[k] k')`. -/
private theorem transcendental_baseChange_X (X : AlgebraicBelyiPair k) :
    letI := X.isDomain_tensorProduct k'
    Transcendental k'
      (algebraMap X (FractionRing (X ⊗[k] k')) (algebraMap (RatFunc k) X RatFunc.X)) := by
  let _ := X.isDomain_tensorProduct k'
  have hx : Transcendental k (algebraMap (RatFunc k) X RatFunc.X) :=
    (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective (RatFunc k) X)).mpr
      RatFunc.transcendental_X
  exact (linearDisjoint_of_isFractionRing_tensorProduct (k := k)).transcendental_algebraMap hx

/-- **Base change of a bundled algebraic Belyi pair** along an arbitrary field extension `k → k'`,
with underlying function field `FractionRing (X ⊗[k] k')`. -/
noncomputable def baseChange (X : AlgebraicBelyiPair k) : AlgebraicBelyiPair k' :=
  letI := X.isDomain_tensorProduct k'
  letI := ratFuncAlgebraOfTranscendental (transcendental_baseChange_X k' X)
  haveI := isScalarTower_ratFuncAlgebraOfTranscendental (transcendental_baseChange_X k' X)
  have hcomp : constantCompositum X k' (FractionRing (X ⊗[k] k')) = ⊤ := by
    rw [constantCompositum_def]
    exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k)
  have hX : algebraMap X (FractionRing (X ⊗[k] k')) (algebraMap (RatFunc k) X RatFunc.X) =
      algebraMap (RatFunc k') (FractionRing (X ⊗[k] k')) RatFunc.X :=
    (algebraMap_ratFuncAlgebraOfTranscendental_X (transcendental_baseChange_X k' X)).symm
  haveI : FiniteDimensional (RatFunc k') (FractionRing (X ⊗[k] k')) :=
    finiteDimensional_ratFunc_of_constantCompositum_eq_top hcomp hX
  { carrier := FractionRing (X ⊗[k] k')
    isAlgebraicBelyiPair := (isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top
      X.isAlgebraicBelyiPair.isIntegrallyClosedIn hcomp hX).mpr X.isAlgebraicBelyiPair }

noncomputable instance (X : AlgebraicBelyiPair k) : Algebra k (X.baseChange k') :=
  ((algebraMap k' (X.baseChange k')).comp (algebraMap k k')).toAlgebra

instance (X : AlgebraicBelyiPair k) : IsScalarTower k k' (X.baseChange k') :=
  .of_algebraMap_eq' rfl

/-- The canonical `k`-algebra embedding `X →ₐ[k] X.baseChange k'` into the base change. -/
noncomputable def toBaseChange (X : AlgebraicBelyiPair k) : X →ₐ[k] X.baseChange k' :=
  letI := X.isDomain_tensorProduct k'
  { algebraMap X (FractionRing (X ⊗[k] k')) with
    commutes' := fun c ↦ by
      change algebraMap X (FractionRing (X ⊗[k] k')) (algebraMap k X c) =
        algebraMap k' (FractionRing (X ⊗[k] k')) (algebraMap k k' c)
      rw [← IsScalarTower.algebraMap_apply k X, ← IsScalarTower.algebraMap_apply k k'] }

@[simp]
theorem toBaseChange_algebraMap_X (X : AlgebraicBelyiPair k) :
    X.toBaseChange k' (algebraMap (RatFunc k) X RatFunc.X) =
      algebraMap (RatFunc k') (X.baseChange k') RatFunc.X :=
  letI := X.isDomain_tensorProduct k'
  (algebraMap_ratFuncAlgebraOfTranscendental_X (transcendental_baseChange_X k' X)).symm

noncomputable instance (X : AlgebraicBelyiPair k) : Algebra X (X.baseChange k') :=
  (X.toBaseChange k').toRingHom.toAlgebra

instance (X : AlgebraicBelyiPair k) : IsScalarTower k X (X.baseChange k') :=
  .of_algebraMap_eq fun c ↦ ((X.toBaseChange k').commutes c).symm

@[simp]
theorem algebraMap_baseChange_X (X : AlgebraicBelyiPair k) :
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
  refine productMap_injective_iff_linearDisjoint.mp ?_
  have heq (z : X ⊗[k] k') :
      Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k X (X.baseChange k'))
        (IsScalarTower.toAlgHom k k' (X.baseChange k')) z =
      Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k X (FractionRing (X ⊗[k] k')))
        (IsScalarTower.toAlgHom k k' (FractionRing (X ⊗[k] k'))) z := by
    induction z using TensorProduct.inductionOn with
    | tmul _ _ => rfl
    | add _ _ hu hv => rw [map_add, map_add, hu, hv]; rfl
  intro u v huv
  exact hinj ((heq u).symm.trans (huv.trans (heq v)))

/-- `X` and `k'` generate `X.baseChange k'` as a field. -/
theorem constantCompositum_baseChange_eq_top (X : AlgebraicBelyiPair k) :
    constantCompositum X k' (X.baseChange k') = ⊤ := by
  let _ := X.isDomain_tensorProduct k'
  have h2 : constantCompositum X k' (FractionRing (X ⊗[k] k')) = ⊤ := by
    rw [constantCompositum_def]
    exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k)
  rw [← IntermediateField.toSubfield_inj, IntermediateField.top_toSubfield, constantCompositum_def,
    IntermediateField.adjoin_toSubfield] at h2 ⊢
  exact h2

/-- Base change of an algebraic Belyi pair preserves its degree over the rational function field. -/
@[simp]
theorem finrank_baseChange (X : AlgebraicBelyiPair k) :
    Module.finrank (RatFunc k') (X.baseChange k') = Module.finrank (RatFunc k) X := by
  have hF : IsFunctionField k X := (IsFunctionField.ratFunc k).finite_extension
  obtain ⟨x₀, hx₀, _⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  have : Algebra.IsGeometricallyReduced k X := isGeometricallyReduced_of_separating hx₀
  exact finrank_ratFunc_eq_of_isGeometricallyReduced X.isAlgebraicBelyiPair.isIntegrallyClosedIn
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
/-- **Full faithfulness of base change on isomorphisms of Belyi pairs** over an algebraically closed
base field `k` (such as `AlgebraicClosure ℚ ⊂ ℂ`). -/
noncomputable def baseChangeAlgEquivEquiv [IsAlgClosed k] (X Y : AlgebraicBelyiPair k) :
    (X ≃ₐ[RatFunc k] Y) ≃ (X.baseChange k' ≃ₐ[RatFunc k'] Y.baseChange k') :=
  ratFuncConstantExtensionAlgEquivEquiv (X.linearDisjoint_baseChange k')
    (X.constantCompositum_baseChange_eq_top k') (Y.linearDisjoint_baseChange k')
    (Y.constantCompositum_baseChange_eq_top k') (X.algebraMap_baseChange_X k')
    (Y.algebraMap_baseChange_X k')

namespace IsoClass

variable (k') in
/-- **Base change of isomorphism classes of algebraic Belyi pairs** along an arbitrary field
extension `k → k'`. -/
noncomputable def baseChange : IsoClass k → IsoClass k' :=
  lift (fun X ↦ mk (X.baseChange k')) fun _ _ e ↦ mk_eq_mk (baseChangeAlgEquiv e)

@[simp]
theorem baseChange_mk (X : AlgebraicBelyiPair k) :
    (mk X).baseChange k' = mk (X.baseChange k') :=
  lift_mk _ _ X

@[simp]
theorem degree_baseChange (c : IsoClass k) : (c.baseChange k').degree = c.degree := by
  induction c using ind with
  | h X => simp [finrank_baseChange]

/-- **Base change of isomorphism classes from an algebraically closed field is injective**: for
instance, two Belyi pairs over `AlgebraicClosure ℚ` become isomorphic over `ℂ` if and only if they
are already isomorphic over `AlgebraicClosure ℚ`. -/
theorem baseChange_injective [IsAlgClosed k] :
    Function.Injective (baseChange (k := k) k') := by
  intro c₁ c₂
  induction c₁ using ind with | h X => ?_
  induction c₂ using ind with | h Y => ?_
  simp only [baseChange_mk, mk_eq_mk_iff]
  rintro ⟨e'⟩
  exact ⟨(baseChangeAlgEquivEquiv k' X Y).symm e'⟩

@[simp]
theorem baseChange_eq_iff [IsAlgClosed k] {c₁ c₂ : IsoClass k} :
    c₁.baseChange k' = c₂.baseChange k' ↔ c₁ = c₂ :=
  (baseChange_injective (k := k) (k' := k')).eq_iff

end IsoClass

end BaseChange

end AlgebraicBelyiPair

end TauCeti
