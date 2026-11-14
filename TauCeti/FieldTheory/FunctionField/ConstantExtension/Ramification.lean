/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Degree
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Place
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Unramified
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.FieldTheory.FunctionField.SeparablyGenerated
import TauCeti.FieldTheory.RatFunc.Map

/-!
# Ramification over the rational function field after extending constants

Let `F` be a field over `k(t)` and let `F' = F · k'` be its compositum with an algebraic
extension `k' / k` of a perfect field, finite or not, carrying the `k'(t)`-algebra structure in
which `t` acts as it does on `F`. Geometrically, `F / k(t)` is a finite map from a curve to the
projective line, and `F' / k'(t)` is its base change to `k'`. This file shows that base change
does not change ramification over the line: a place `Q'` of `F'` has the same ramification index
over `k'(t)` as the place `Q` of `F` below it has over `k(t)`, and the place of `k'(t)` below `Q'`
gives every polynomial in `t` with coefficients in `k` the same order as the place of `k(t)`
below `Q`.

Both statements come from comparing the orders at `Q'` of a polynomial in `t` computed through
`F` and through `k'(t)`. The constant field extension `F' / F` is unramified
(`TauCeti.Place.ramificationIdx_eq_one_of_constantCompositum_eq_top`), so through `F` the order is
`e(Q ∣ k(t))` times the order at the place of `k(t)` below `Q`, and through `k'(t)` it is
`e(Q' ∣ k'(t))` times the order at the place of `k'(t)` below `Q'`. At the place at infinity the
polynomial `t` has a simple pole on both sides. At the place of an irreducible `q` the polynomial
`q` has order one, and it has order at most one at every finite place of `k'(t)`, because `q`
stays squarefree over `k'`, `k` being perfect.

For arbitrary (possibly transcendental) extensions `k' / k`, places of `F'` trivial on `F` are
unramified over `k'(t)` when `F / k(t)` is finite separable, while places contracting to `Q` on `F`
preserve `e(Q ∣ k(t))` and polynomial orders whenever `k` is exact in `F`.

For a Belyi map this is what makes being unramified outside `t = 0`, `t = 1` and `t = ∞`
invariant under extension of the constant field
(`TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`).

## Main results

* `TauCeti.Place.ramificationIdx_ratFunc_eq_of_constantCompositum_eq_top`:
  `e(Q' ∣ k'(t)) = e(Q ∣ k(t))`.
* `TauCeti.Place.ord_restrict_algebraMap_eq_of_constantCompositum_eq_top`: the places of `k(t)`
  and `k'(t)` below `Q'` give a polynomial over `k` the same order.
* `TauCeti.Place.ramificationIdx_ratFunc_eq_one_of_isTrivialOn` and
  `TauCeti.Place.ramificationIdx_ratFunc_eq_of_integers_comap_eq`: ramification under arbitrary
  constant extensions.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.1.6 and Theorem 3.6.3.
-/

public section

open Polynomial
open scoped IntermediateField

namespace TauCeti

namespace Place

section Algebraic

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [Algebra.IsIntegral (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']
  [Algebra.IsIntegral (RatFunc k') F'] [Algebra.IsIntegral F F']

omit [Algebra.IsIntegral (RatFunc k) F] [Algebra.IsIntegral (RatFunc k') F']
  [Algebra.IsIntegral F F'] in
/-- A polynomial in `t` over `k` has the same image in `F'` through `F` as through `k'(t)`. -/
private theorem algebraMap_algebraMap_polynomial
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (p : k[X]) :
    algebraMap F F' (algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) p)) =
      algebraMap (RatFunc k') F' (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) := by
  have h₁ := aeval_algHom_apply
    ((IsScalarTower.toAlgHom k F F').comp (IsScalarTower.toAlgHom k (RatFunc k) F)) RatFunc.X p
  have h₂ := aeval_algHom_apply (IsScalarTower.toAlgHom k' (RatFunc k') F') RatFunc.X
    (p.map (algebraMap k k'))
  simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
    RatFunc.aeval_X_left_eq_algebraMap] at h₁ h₂
  rw [← h₁, ← h₂, hX, aeval_map_algebraMap]

variable [Algebra.IsSeparable k k']

/-- The order at `Q'` of a polynomial in `t`, computed through `F` and through `k'(t)`. -/
private theorem ramificationIdx_mul_ord_eq (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (Q' : Place k' F') (p : k[X]) :
    (ramificationIdx (RatFunc k) (Q'.restrict k F) : ℤ) *
        ((Q'.restrict k F).restrict k (RatFunc k)).ord (algebraMap k[X] (RatFunc k) p) =
      ramificationIdx (RatFunc k') Q' * (Q'.restrict k' (RatFunc k')).ord
        (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) := by
  rw [← ord_algebraMap_restrict k (RatFunc k) (Q'.restrict k F),
    ← ord_algebraMap_restrict k' (RatFunc k') Q', ← algebraMap_algebraMap_polynomial hX,
    ord_algebraMap_restrict k F Q',
    ramificationIdx_eq_one_of_constantCompositum_eq_top (k := k) hcomp,
    Nat.cast_one, one_mul]

variable [PerfectField k]

/-- **Extending constants does not change ramification over the line**: if `F' = F · k'` for an
algebraic extension `k' / k` of a perfect field and `t` acts on `F'` as it does on `F`, then every
place `Q'` of `F'` has the same ramification index over `k'(t)` as the place of `F` below it has
over `k(t)`. -/
theorem ramificationIdx_ratFunc_eq_of_constantCompositum_eq_top
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (Q' : Place k' F') :
    ramificationIdx (RatFunc k') Q' = ramificationIdx (RatFunc k) (Q'.restrict k F) := by
  have he := ramificationIdx_pos (RatFunc k) (Q'.restrict k F)
  have hord := ramificationIdx_mul_ord_eq hcomp hX Q'
  rcases eq_infty_or_exists_eq_adicOfIrreducible ((Q'.restrict k F).restrict k (RatFunc k)) with
    hP | ⟨q, hq, hP⟩
  · -- At infinity `t` has a simple pole, below `Q'` in `k(t)` and hence also in `k'(t)`.
    have h := hord X
    rw [Polynomial.map_X, RatFunc.algebraMap_X, RatFunc.algebraMap_X, hP, ord_infty,
      RatFunc.intDegree_X] at h
    have hP' : Q'.restrict k' (RatFunc k') = infty k' := by
      refine X_notMem_integers_iff_eq_infty.mp fun hmem ↦ ?_
      have := (Q'.restrict k' (RatFunc k')).mem_integers_iff_ord_nonneg.mp hmem
      nlinarith
    rw [hP', ord_infty, RatFunc.intDegree_X] at h
    omega
  -- At the place of `q`, the order of `q` is one, and `q` stays squarefree over `k'`.
  have h := hord q
  rw [hP, ord_adicOfIrreducible_algebraMap_irreducible hq hq, ite_eq_left (Associated.refl q),
    mul_one] at h
  have hsq : Squarefree (q.map (algebraMap k k')) :=
    (PerfectField.separable_of_irreducible hq).map.squarefree
  rcases eq_infty_or_exists_eq_adicOfIrreducible (Q'.restrict k' (RatFunc k')) with
    hP' | ⟨q', hq', hP'⟩
  · rw [hP', ord_infty, RatFunc.intDegree_polynomial] at h
    nlinarith
  rw [hP', ord_adicOfIrreducible_algebraMap_of_squarefree hq' hsq] at h
  split_ifs at h <;> omega

/-- **Extending constants does not change orders of polynomials in `t`**: under the hypotheses of
`TauCeti.Place.ramificationIdx_ratFunc_eq_of_constantCompositum_eq_top`, the place of `k(t)` below
the place `Q` of `F` under `Q'` and the place of `k'(t)` below `Q'` give every polynomial in `t`
over `k` the same order. -/
theorem ord_restrict_algebraMap_eq_of_constantCompositum_eq_top
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (Q' : Place k' F') (p : k[X]) :
    ((Q'.restrict k F).restrict k (RatFunc k)).ord (algebraMap k[X] (RatFunc k) p) =
      (Q'.restrict k' (RatFunc k')).ord
        (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) := by
  have h := ramificationIdx_mul_ord_eq hcomp hX Q' p
  rw [ramificationIdx_ratFunc_eq_of_constantCompositum_eq_top hcomp hX Q'] at h
  exact mul_left_cancel₀ (by exact_mod_cast (ramificationIdx_pos _ _).ne') h

end Algebraic

section ArbitraryExtension

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']

private noncomputable def ratFuncMapRingHom (k₀ k₁ : Type*) [Field k₀] [Field k₁] [Algebra k₀ k₁] :
    RatFunc k₀ →+* RatFunc k₁ :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k₀ k₁))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap k₀ k₁).injective))

private theorem algebraMap_ratFuncMapRingHom
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (r : RatFunc k) :
    algebraMap (RatFunc k') F' (ratFuncMapRingHom k k' r) =
      algebraMap F F' (algebraMap (RatFunc k) F r) := by
  have h : (algebraMap (RatFunc k') F').comp (ratFuncMapRingHom k k') =
      (algebraMap F F').comp (algebraMap (RatFunc k) F) :=
    IsFractionRing.ringHom_ext (A := k[X]) fun p ↦ by
      simp only [RingHom.comp_apply, ratFuncMapRingHom, RatFunc.mapRingHom_algebraMap,
        Polynomial.coe_mapRingHom, algebraMap_algebraMap_polynomial hX]
  exact congr($h r)

private theorem ord_restrict_ratFuncMapRingHom_eq_zero_of_isTrivialOn
    [Algebra.IsIntegral (RatFunc k') F']
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q' : Place k' F'}
    (hQ' : Q'.valuation.IsTrivialOn F) {r : RatFunc k} (hr : r ≠ 0) :
    (Q'.restrict k' (RatFunc k')).ord (ratFuncMapRingHom k k' r) = 0 := by
  have hf0 : algebraMap (RatFunc k) F r ≠ 0 := (_root_.map_ne_zero _).mpr hr
  have hord0 : Q'.ord (algebraMap F F' (algebraMap (RatFunc k) F r)) = 0 :=
    (Q'.ord_eq_iff_valuation_eq_exp_neg ((_root_.map_ne_zero _).mpr hf0)).mpr
      (by simp [hQ'.eq_one _ hf0])
  rw [← algebraMap_ratFuncMapRingHom hX, ord_algebraMap_restrict k' (RatFunc k') Q'] at hord0
  exact (mul_eq_zero.mp hord0).resolve_left
    (by exact_mod_cast (ramificationIdx_pos (RatFunc k') Q').ne')

/-- **At a place of `F'` trivial on `F`, every nonzero polynomial over `k` has order zero.** -/
theorem ord_restrict_algebraMap_eq_zero_of_isTrivialOn [Algebra.IsIntegral (RatFunc k') F']
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q' : Place k' F'}
    (hQ' : Q'.valuation.IsTrivialOn F) {p : k[X]} (hp : p ≠ 0) :
    (Q'.restrict k' (RatFunc k')).ord
      (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) = 0 :=
  have hr : algebraMap k[X] (RatFunc k) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hp
  by simpa [ratFuncMapRingHom, RatFunc.mapRingHom_algebraMap] using
    ord_restrict_ratFuncMapRingHom_eq_zero_of_isTrivialOn hX hQ' hr

private theorem adjoin_primitive_ratFunc_eq_top (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {y : F} (hy : (RatFunc k)⟮y⟯ = ⊤) :
    (RatFunc k')⟮algebraMap F F' y⟯ = ⊤ := by
  let E := (RatFunc k')⟮algebraMap F F' y⟯
  let L : IntermediateField (RatFunc k) F :=
    (E.toSubfield.comap (algebraMap F F')).toIntermediateField fun r ↦ by
      rw [Subfield.mem_comap, ← algebraMap_ratFuncMapRingHom hX]; exact E.algebraMap_mem _
  have hL : L = ⊤ := top_le_iff.mp (hy.symm.le.trans <|
    IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self _ _))
  let M : IntermediateField F F' :=
    { E.toSubfield with
      algebraMap_mem' := fun x ↦ by
        have hx : x ∈ L.toSubfield := (IntermediateField.mem_toSubfield L x).mpr (hL ▸ trivial)
        rwa [Subfield.toIntermediateField_toSubfield, Subfield.mem_comap] at hx }
  have hM : constantCompositum F k' F' ≤ M := (constantCompositum_le_iff F k' F').mpr fun c ↦ by
    change algebraMap k' F' c ∈ E.toSubfield
    rw [IsScalarTower.algebraMap_apply k' (RatFunc k') F']; exact E.algebraMap_mem _
  exact top_le_iff.mp fun z _ ↦ hM (hcomp ▸ IntermediateField.mem_top)

/-- Places of `F' = F · k'` trivial on `F` are unramified over `k'(t)` (`F / k(t)` separable). -/
theorem ramificationIdx_ratFunc_eq_one_of_isTrivialOn [FiniteDimensional (RatFunc k) F]
    [Algebra.IsSeparable (RatFunc k) F] (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q' : Place k' F'}
    (hQ' : Q'.valuation.IsTrivialOn F) :
    ramificationIdx (RatFunc k') Q' = 1 := by
  have : FiniteDimensional (RatFunc k') F' :=
    finiteDimensional_ratFunc_of_constantCompositum_eq_top hcomp hX
  obtain ⟨y, hy⟩ := Field.exists_primitive_element (RatFunc k) F
  let y' : F' := algebraMap F F' y
  have hgen : (RatFunc k')⟮y'⟯ = ⊤ := adjoin_primitive_ratFunc_eq_top hcomp hX hy
  let p := minpoly (RatFunc k) y
  let p' := p.map (ratFuncMapRingHom k k')
  have hcomp_rh : (algebraMap (RatFunc k') F').comp (ratFuncMapRingHom k k') =
      (algebraMap F F').comp (algebraMap (RatFunc k) F) :=
    RingHom.ext (algebraMap_ratFuncMapRingHom hX)
  have hmap_eval (q : (RatFunc k)[X]) :
      aeval y' (q.map (ratFuncMapRingHom k k')) = algebraMap F F' (aeval y q) := by
    rw [aeval_def, eval₂_map, hcomp_rh,
      ← hom_eval₂ q (algebraMap (RatFunc k) F) (algebraMap F F') y, ← aeval_def]
  have hroot : aeval y' p' = 0 := by rw [hmap_eval, minpoly.aeval, map_zero]
  have : Algebra.IsSeparable (RatFunc k') F' := by
    rw [← IntermediateField.isSeparable_top, ← hgen,
      IntermediateField.isSeparable_adjoin_simple_iff_isSeparable]
    exact (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable (RatFunc k) y)).of_dvd
      (minpoly.dvd (RatFunc k') y' hroot)
  have hpcoeff : ∀ i, p'.coeff i ∈ (Q'.restrict k' (RatFunc k')).integers := fun i ↦ by
    rw [coeff_map]
    rcases eq_or_ne (p.coeff i) 0 with h0 | h0
    · simp [h0]
    · rw [(Q'.restrict k' (RatFunc k')).mem_integers_iff_ord_nonneg,
        ord_restrict_ratFuncMapRingHom_eq_zero_of_isTrivialOn hX hQ' h0]
  have hderiv : Q'.valuation (aeval y' (derivative p')) = 1 := by
    rw [derivative_map, hmap_eval]
    exact hQ'.eq_one _ ((Algebra.IsSeparable.isSeparable (RatFunc k) y).aeval_derivative_ne_zero
      (minpoly.aeval (RatFunc k) y))
  have hunram : Algebra.IsUnramifiedAt (Q'.restrict k' (RatFunc k')).integers
      (centerIntegralClosure k' (RatFunc k') Q').asIdeal :=
    (differentExponent_eq_zero_iff k' (RatFunc k') Q').mp
      (differentExponent_eq_zero_of_valuation_aeval_derivative_eq_one k' (RatFunc k') hgen
        ((minpoly.monic (Algebra.IsSeparable.isIntegral (RatFunc k) y)).map _) hpcoeff hroot hderiv)
  rw [ramificationIdx_eq_ramificationIdx_center (R := (Q'.restrict k' (RatFunc k')).integers)
    k' (RatFunc k') Q' (algebraMap_mem_integers_of_mem_integralClosure k' (RatFunc k') Q'),
    ← centerIntegralClosure_def]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

private theorem ramificationIdx_mul_ord_eq_of_integers_comap_eq [PerfectField k]
    [FiniteDimensional (RatFunc k) F] [Algebra.IsIntegral (RatFunc k') F']
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q : Place k F} {Q' : Place k' F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) (p : k[X]) :
    (ramificationIdx (RatFunc k) Q : ℤ) *
        (Q.restrict k (RatFunc k)).ord (algebraMap k[X] (RatFunc k) p) =
      ramificationIdx (RatFunc k') Q' * (Q'.restrict k' (RatFunc k')).ord
        (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) := by
  have hF : IsFunctionField k F := (IsFunctionField.ratFunc k).finite_extension
  obtain ⟨x₀, hx₀, _⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  have : Algebra.IsGeometricallyReduced k F := isGeometricallyReduced_of_separating hx₀
  rw [← ord_algebraMap_restrict k (RatFunc k) Q, ← ord_algebraMap_restrict k' (RatFunc k') Q',
    ← algebraMap_algebraMap_polynomial hX,
    ord_algebraMap_eq_of_integers_comap_eq hF hex
      (linearDisjoint_of_isGeometricallyReduced_ratFunc hex hX) hcomp hQ']

/-- Extending constants by an arbitrary extension preserves ramification over `k(t)` at contracting
places (`k` perfect and exact in `F`). -/
theorem ramificationIdx_ratFunc_eq_of_integers_comap_eq [PerfectField k]
    [FiniteDimensional (RatFunc k) F]
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q : Place k F} {Q' : Place k' F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) :
    ramificationIdx (RatFunc k') Q' = ramificationIdx (RatFunc k) Q := by
  have : FiniteDimensional (RatFunc k') F' :=
    finiteDimensional_ratFunc_of_constantCompositum_eq_top hcomp hX
  have he := ramificationIdx_pos (RatFunc k) Q
  have hord := ramificationIdx_mul_ord_eq_of_integers_comap_eq hex hcomp hX hQ'
  rcases eq_infty_or_exists_eq_adicOfIrreducible (Q.restrict k (RatFunc k)) with hP | ⟨q, hq, hP⟩
  · have h := hord X
    rw [Polynomial.map_X, RatFunc.algebraMap_X, RatFunc.algebraMap_X, hP, ord_infty,
      RatFunc.intDegree_X] at h
    have hP' : Q'.restrict k' (RatFunc k') = infty k' := X_notMem_integers_iff_eq_infty.mp fun hm ↦
      by have := (Q'.restrict k' (RatFunc k')).mem_integers_iff_ord_nonneg.mp hm; nlinarith
    rw [hP', ord_infty, RatFunc.intDegree_X] at h; omega
  have h := hord q
  rw [hP, ord_adicOfIrreducible_algebraMap_irreducible hq hq, ite_eq_left (Associated.refl q),
    mul_one] at h
  have hsq : Squarefree (q.map (algebraMap k k')) :=
    (PerfectField.separable_of_irreducible hq).map.squarefree
  rcases eq_infty_or_exists_eq_adicOfIrreducible (Q'.restrict k' (RatFunc k')) with
    hP' | ⟨q', hq', hP'⟩
  · rw [hP', ord_infty, RatFunc.intDegree_polynomial] at h; nlinarith
  rw [hP', ord_adicOfIrreducible_algebraMap_of_squarefree hq' hsq] at h
  split_ifs at h <;> omega

/-- Extending constants preserves orders of polynomials over `k` at contracting places. -/
theorem ord_restrict_algebraMap_eq_of_integers_comap_eq [PerfectField k]
    [FiniteDimensional (RatFunc k) F] [Algebra.IsIntegral (RatFunc k') F']
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q : Place k F} {Q' : Place k' F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) (p : k[X]) :
    (Q.restrict k (RatFunc k)).ord (algebraMap k[X] (RatFunc k) p) =
      (Q'.restrict k' (RatFunc k')).ord
        (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) := by
  have h := ramificationIdx_mul_ord_eq_of_integers_comap_eq hex hcomp hX hQ' p
  rw [ramificationIdx_ratFunc_eq_of_integers_comap_eq hex hcomp hX hQ'] at h
  exact mul_left_cancel₀ (by exact_mod_cast (ramificationIdx_pos _ _).ne') h

end ArbitraryExtension

end Place

end TauCeti
