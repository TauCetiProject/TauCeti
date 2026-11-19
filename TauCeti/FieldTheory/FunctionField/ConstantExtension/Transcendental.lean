/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.LinearDisjoint
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
public import Mathlib.FieldTheory.RatFunc.Basic

import TauCeti.FieldTheory.FunctionField.ConstantExtension.Ramification
import TauCeti.FieldTheory.FunctionField.Different.Derivative
import TauCeti.FieldTheory.FunctionField.Different.Tame
import TauCeti.FieldTheory.FunctionField.Divisor.ProductFormula
import TauCeti.FieldTheory.FunctionField.Frobenius
import TauCeti.FieldTheory.FunctionField.Place.Degree
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus
import TauCeti.FieldTheory.RatFunc.Map
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Arbitrary and transcendental constant field extensions

Let `F / k` be an algebraic function field and `k' / k` an arbitrary field extension, possibly
transcendental, inside a common overfield `F' = F · k'`. Unlike the algebraic case treated in
`TauCeti.FieldTheory.FunctionField.ConstantExtension.TensorProduct` and
`TauCeti.FieldTheory.FunctionField.ConstantExtension.Fibre`, `F ⊗[k] k'` need not be a field and
`F' / F` need not be integral: a place `Q'` of `F' / k'` may be trivial on `F`
(`ramificationIdx F Q' = 0`), corresponding geometrically to a point of the base-changed curve
over `k'` whose image does not specialize to a closed point over `k`.

The foundational tensor-fraction-field presentation, linear disjointness, and exact-constants
theorems live in `TauCeti.FieldTheory.FunctionField.ConstantExtension.FractionField`; normalized
place restriction `TauCeti.Place.restrictOfRamificationIdxNeZero` lives in
`TauCeti.FieldTheory.FunctionField.Place.Extension.Basic`; and the general ramification
multiplicativity and polynomial-order comparison over rational function fields live in
`TauCeti.FieldTheory.FunctionField.ConstantExtension.Ramification`.

This file builds the global and local comparison across an arbitrary constant extension:

1. **Unramifiedness of constant extensions.** Over a perfect field `k`, every place `Q'` of
   `F' / k'` nontrivial on `F` (`h : ramificationIdx F Q' ≠ 0`) admits a local monogenic
   generator of `F` over a uniformizer at `Q'.restrictOfRamificationIdxNeZero k h` that stays
   unramified in `F'`, forcing `ramificationIdx F Q' = 1`
   (`TauCeti.Place.ramificationIdx_eq_one_of_ramificationIdx_ne_zero`).
   Over a rational function field `k(t)`, places nontrivial on `F` therefore preserve ramification
   index over `k(t)` (`TauCeti.Place.ramificationIdx_ratFunc_eq_of_ramificationIdx_ne_zero`), while
   places trivial on `F` give every polynomial over `k` order zero and are unramified over `k'(t)`
   whenever `F / k(t)` is finite separable
   (`TauCeti.Place.ramificationIdx_ratFunc_eq_one_of_ramificationIdx_eq_zero`).

2. **Fibres and degree sum.** Using a function with a single pole at `P`, the places of `F' / k'`
   nontrivial on `F` and restricting to `P` coincide with the poles of that function in `F'`; they
   form a nonempty finite set whose degrees sum to `deg P`
   (`TauCeti.Place.finsum_degree_restrictOfRamificationIdxNeZero_eq_degree`).

## Main results

* `TauCeti.Place.ramificationIdx_eq_one_of_ramificationIdx_ne_zero`: over perfect `k`, places of
  `F' / k'` nontrivial on `F` satisfy `ramificationIdx F P' = 1`.
* `TauCeti.Place.ramificationIdx_ratFunc_eq_of_ramificationIdx_ne_zero`,
  `TauCeti.Place.ord_restrict_algebraMap_eq_zero_of_ramificationIdx_eq_zero`, and
  `TauCeti.Place.ramificationIdx_ratFunc_eq_one_of_ramificationIdx_eq_zero`: comparison of
  ramification and orders over `k(t)` and `k'(t)` at places nontrivial and trivial on `F`.
* `TauCeti.Place.finite_setOf_restrictOfRamificationIdxNeZero_eq`,
  `TauCeti.Place.finsum_degree_restrictOfRamificationIdxNeZero_eq_degree`,
  `TauCeti.Place.exists_restrictOfRamificationIdxNeZero_eq`, and
  `TauCeti.Place.ncard_setOf_restrictOfRamificationIdxNeZero_eq_of_isAlgClosed`: finiteness,
  nonemptiness, and degree/cardinality formulas for fibres of `restrictOfRamificationIdxNeZero`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6.
* S. Lang, *Algebra*, rev. 3rd ed., GTM 211, Springer, 2002, Chapter VIII, §3–4.
-/

public section

open Polynomial

open scoped IntermediateField nonZeroDivisors

namespace TauCeti

namespace Place

section Restrict

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

omit [Algebra k k'] [Algebra k F] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] in
/-- Pushing a separable monogenic generator `y` of `F / B` with `P'`-unit derivative to `F' / B'`
along `F' = F · k'` shows that `P'` is unramified over `B'`. -/
private theorem ramificationIdx_eq_one_of_primitive_of_constantCompositum_eq_top
    {B B' : Type*} [Field B] [Field B'] [Algebra B F] [Algebra k' B'] [Algebra B' F']
    [IsScalarTower k' B' F'] [Algebra.IsSeparable B F]
    [FiniteDimensional B' F'] (hcomp : constantCompositum F k' F' = ⊤) (φ : B →+* B')
    (hφ : (algebraMap B' F').comp φ = (algebraMap F F').comp (algebraMap B F))
    {P' : Place k' F'} {y : F} (hy_gen : B⟮y⟯ = ⊤)
    (hy_coeff : ∀ i, φ ((minpoly B y).coeff i) ∈ (P'.restrict k' B').integers)
    (hy_der : P'.valuation (algebraMap F F' (aeval y (derivative (minpoly B y)))) = 1) :
    ramificationIdx B' P' = 1 := by
  let y' := algebraMap F F' y
  let ψ : B'[X] := (minpoly B y).map φ
  have hgen' : B'⟮y'⟯ = ⊤ := by
    rw [← IntermediateField.toSubfield_inj, IntermediateField.top_toSubfield, eq_top_iff]
    let E : Subfield F' := (B'⟮y'⟯).toSubfield
    have hF_top : E.comap (algebraMap F F') = ⊤ := by
      have hy_top : (B⟮y⟯).toSubfield = ⊤ := by rw [hy_gen, IntermediateField.top_toSubfield]
      rw [IntermediateField.adjoin_toSubfield] at hy_top
      rw [eq_top_iff, ← hy_top, Subfield.closure_le, Set.union_subset_iff]
      refine ⟨?_, Set.singleton_subset_iff.mpr (IntermediateField.mem_adjoin_simple_self B' y')⟩
      rintro _ ⟨u, rfl⟩
      have hu : algebraMap F F' (algebraMap B F u) = algebraMap B' F' (φ u) :=
        (congr($hφ u)).symm
      exact Subfield.mem_comap.mpr (hu ▸ B'⟮y'⟯.algebraMap_mem (φ u))
    have hcomp_top : (constantCompositum F k' F').toSubfield = ⊤ := by
      rw [hcomp, IntermediateField.top_toSubfield]
    rw [constantCompositum_def, IntermediateField.adjoin_toSubfield] at hcomp_top
    rw [← hcomp_top, Subfield.closure_le, Set.union_subset_iff]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨f, rfl⟩
      exact Subfield.mem_comap.mp (hF_top.symm ▸ trivial : f ∈ E.comap (algebraMap F F'))
    · rintro _ ⟨c, rfl⟩
      rw [SetLike.mem_coe, IsScalarTower.algebraMap_apply k' B' F']
      exact B'⟮y'⟯.algebraMap_mem (algebraMap k' B' c)
  have hψ_root : aeval y' ψ = 0 := by
    dsimp only [y']
    rw [aeval_def, eval₂_map, hφ, ← Polynomial.hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hder_eq : aeval y' (derivative ψ) =
      algebraMap F F' (aeval y (derivative (minpoly B y))) := by
    have hmap : (derivative ψ).map (algebraMap B' F') =
        (derivative (minpoly B y)).map ((algebraMap F F').comp (algebraMap B F)) := by
      rw [← derivative_map, Polynomial.map_map, hφ, derivative_map]
    dsimp only [y']
    rw [aeval_def, ← eval_map, hmap, eval_map, ← Polynomial.hom_eval₂, ← aeval_def]
  have : Algebra.IsSeparable B' F' := by
    have hsep_ψ : ψ.Separable :=
      Polynomial.Separable.map (Algebra.IsSeparable.isSeparable B y)
    rw [← separableClosure.eq_top_iff, eq_top_iff, ← hgen', IntermediateField.adjoin_simple_le_iff,
      mem_separableClosure_iff]
    exact hsep_ψ.of_dvd (minpoly.dvd B' y' hψ_root)
  have hd'_zero : differentExponent k' B' P' = 0 :=
    differentExponent_eq_zero_of_valuation_aeval_derivative_eq_one k' B' hgen'
      ((minpoly.monic (Algebra.IsSeparable.isIntegral B y)).map φ)
      (fun i ↦ by rw [coeff_map]; exact hy_coeff i) hψ_root (hder_eq ▸ hy_der)
  exact ((ramificationIdx_eq_one_and_isSeparable_iff_isUnramifiedAt k' B' P').mpr
    ((differentExponent_eq_zero_iff k' B' P').mp hd'_zero)).1

/-- **Every place nontrivial on `F` in an arbitrary constant field extension has ramification index
one** over a perfect base field `k`: choosing a uniformizer `t` of `P` in `F`, `F / k(t)` is finite
separable and unramified at `P`, so a local monogenic generator at `P` remains unramified at `P'`
over `k'(t)` while `t` keeps order one in `k'(t)`. -/
theorem ramificationIdx_eq_one_of_ramificationIdx_ne_zero [PerfectField k]
    (hF : IsFunctionField k F) (hcomp : constantCompositum F k' F' = ⊤) {P' : Place k' F'}
    (h : ramificationIdx F P' ≠ 0) :
    ramificationIdx F P' = 1 := by
  let P := P'.restrictOfRamificationIdxNeZero k h
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  rw [isUniformizer_iff_ord_eq_one] at ht
  obtain ⟨ht_tr, hsep⟩ := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  have : FiniteDimensional k⟮t⟯ F := hF.finiteDimensional_adjoin ht_tr
  have : Algebra.IsSeparable k⟮t⟯ F := hsep
  have ht_ord' : P'.ord (algebraMap F F' t) = ramificationIdx F P' := by
    rw [ord_algebraMap_restrictOfRamificationIdxNeZero (k := k) P' h, ht, mul_one]
  have ht'_tr : Transcendental k' (algebraMap F F' t) :=
    P'.transcendental_of_ord_ne_zero (by rw [ht_ord']; exact_mod_cast h)
  -- `P` is unramified over `k(t)` because `t ∈ k(t)` has order `1` at `P` and `k` is perfect.
  have he_kt : ramificationIdx k⟮t⟯ P = 1 := by
    have h1 := ord_algebraMap_restrict k k⟮t⟯ P (IntermediateField.AdjoinSimple.gen k t)
    have hgen_coe : algebraMap k⟮t⟯ F (IntermediateField.AdjoinSimple.gen k t) = t := rfl
    rw [hgen_coe, ht] at h1
    have hdvd : (ramificationIdx k⟮t⟯ P : ℤ) ∣ 1 := ⟨_, h1⟩
    exact Int.ofNat_inj.mp (Int.eq_one_of_dvd_one (Nat.cast_nonneg _) hdvd)
  have : FiniteDimensional k P.ResidueField := P.finiteDimensional_residueField hF
  have : IsScalarTower k (P.restrict k k⟮t⟯).ResidueField P.ResidueField :=
    .of_algebraMap_eq fun c ↦ (algebraMap_residueField_algebraMap (k := k) (F := k⟮t⟯) P c).symm
  have hsep_res : Algebra.IsSeparable (P.restrict k k⟮t⟯).ResidueField P.ResidueField :=
    Algebra.isSeparable_tower_top_of_isSeparable k (P.restrict k k⟮t⟯).ResidueField P.ResidueField
  have hd_zero : differentExponent k k⟮t⟯ P = 0 :=
    (differentExponent_eq_zero_iff k k⟮t⟯ P).mpr
      ((ramificationIdx_eq_one_and_isSeparable_iff_isUnramifiedAt k k⟮t⟯ P).mp ⟨he_kt, hsep_res⟩)
  obtain ⟨y, hy_gen, hy_coeff, hy_der⟩ :=
    exists_adjoin_eq_top_and_valuation_aeval_derivative_minpoly_eq_one k k⟮t⟯ hd_zero
  -- Push the local monogenic generator `y` and its minimal polynomial over `k(t)` to `F' / k'(t')`.
  let t' := algebraMap F F' t
  have hkt_le : k⟮t⟯ ≤ (k'⟮t'⟯.toSubfield.comap (algebraMap F F')).toIntermediateField
      (fun c ↦ by
        rw [Subfield.mem_comap, ← IsScalarTower.algebraMap_apply k F F',
          IsScalarTower.algebraMap_apply k k' F']
        exact k'⟮t'⟯.algebraMap_mem (algebraMap k k' c)) :=
    IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self k' t')
  let φ : k⟮t⟯ →+* k'⟮t'⟯ :=
    ((algebraMap F F').comp (algebraMap k⟮t⟯ F)).codRestrict k'⟮t'⟯.toSubring fun u ↦ hkt_le u.2
  have hφ_coe (u : k⟮t⟯) : algebraMap k'⟮t'⟯ F' (φ u) = algebraMap F F' (u : F) := rfl
  have : FiniteDimensional k'⟮t'⟯ F' :=
    finiteDimensional_adjoin_simple_of_constantCompositum_eq_top (k := k) hcomp t
  have hder_val : P'.valuation (algebraMap F F' (aeval y (derivative (minpoly k⟮t⟯ y)))) = 1 := by
    have hne : aeval y (derivative (minpoly k⟮t⟯ y)) ≠ 0 := fun h0 ↦ by simp [h0] at hy_der
    have hord0 : P.ord (aeval y (derivative (minpoly k⟮t⟯ y))) = 0 := by
      rw [P.ord_eq_iff_valuation_eq_exp_neg hne, neg_zero, WithZero.exp_zero, hy_der]
    have hord0' : P'.ord (algebraMap F F' (aeval y (derivative (minpoly k⟮t⟯ y)))) = 0 := by
      rw [ord_algebraMap_restrictOfRamificationIdxNeZero (k := k) P' h, hord0, mul_zero]
    exact (P'.ord_eq_iff_valuation_eq_exp_neg
      ((_root_.map_ne_zero (algebraMap F F')).mpr hne)).mp hord0' |>.trans (by simp)
  have he' : ramificationIdx k'⟮t'⟯ P' = 1 :=
    ramificationIdx_eq_one_of_primitive_of_constantCompositum_eq_top hcomp φ (RingHom.ext hφ_coe)
      hy_gen (fun i ↦ by
        rw [mem_integers_restrict_iff, hφ_coe,
          ← mem_integers_restrictOfRamificationIdxNeZero_iff (k := k) P' h]
        exact (mem_integers_restrict_iff k k⟮t⟯ P _).mp (hy_coeff i)) hder_val
  -- In `k'(t')`, `t'` has positive order at `P'.restrict k' k'(t')`, hence order `1`.
  let T : k'⟮t'⟯ := IntermediateField.AdjoinSimple.gen k' t'
  have hordT : P'.ord t' = (P'.restrict k' k'⟮t'⟯).ord T := by
    simpa [he', T] using ord_algebraMap_restrict k' k'⟮t'⟯ P' T
  let eRF := RatFunc.algEquivOfTranscendental t' ht'_tr
  let R : Place k' (RatFunc k') := (P'.restrict k' k'⟮t'⟯).map eRF.symm
  have hRX : R.ord RatFunc.X = (P'.restrict k' k'⟮t'⟯).ord T := by
    have heX : eRF RatFunc.X = T := Subtype.ext (RatFunc.algEquivOfTranscendental_X t' ht'_tr)
    simpa only [R, ord_map, AlgEquiv.symm_symm] using
      congr_arg (P'.restrict k' k'⟮t'⟯).ord heX
  have hRX_pos : 0 < R.ord RatFunc.X := by
    rw [hRX, ← hordT, ht_ord']
    exact_mod_cast Nat.pos_of_ne_zero h
  have hRX_eq : R.ord RatFunc.X = 1 := by
    rcases eq_infty_or_exists_eq_adicOfIrreducible R with hR | ⟨q, hq, hR⟩
    · rw [hR, ord_infty, RatFunc.intDegree_X] at hRX_pos
      omega
    · rw [hR, ← RatFunc.algebraMap_X,
        ord_adicOfIrreducible_algebraMap_irreducible hq irreducible_X] at hRX_pos ⊢
      split_ifs at hRX_pos ⊢ <;> omega
  have : (ramificationIdx F P' : ℤ) = 1 := by
    rw [← ht_ord', hordT, ← hRX, hRX_eq]
  exact_mod_cast this

end Restrict

section RatFunc

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [Algebra.IsIntegral (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F'] [Algebra.IsIntegral (RatFunc k') F']

/-- **Ramification over `k'(t)` at places nontrivial on `F` in an arbitrary constant extension.** -/
theorem ramificationIdx_ratFunc_eq_of_ramificationIdx_ne_zero [PerfectField k]
    (hF : IsFunctionField k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q' : Place k' F'}
    (h : ramificationIdx F Q' ≠ 0) :
    ramificationIdx (RatFunc k') Q' =
      ramificationIdx (RatFunc k) (Q'.restrictOfRamificationIdxNeZero k h) := by
  rw [ramificationIdx_ratFunc_eq_mul_of_ramificationIdx_ne_zero hX h,
    ramificationIdx_eq_one_of_ramificationIdx_ne_zero hF hcomp h, one_mul]

omit [Algebra.IsIntegral (RatFunc k) F] in
/-- At a place `Q'` of `F'` trivial on `F`, every polynomial over `k` has order zero at the place
of `k'(t)` below `Q'`. -/
theorem ord_restrict_algebraMap_eq_zero_of_ramificationIdx_eq_zero
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q' : Place k' F'}
    (h : ramificationIdx F Q' = 0) (p : k[X]) :
    (Q'.restrict k' (RatFunc k')).ord
      (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) = 0 := by
  have hord0 := ord_algebraMap_eq_zero_of_ramificationIdx_eq_zero h
    (algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) p))
  rw [algebraMap_algebraMap_polynomial hX, ord_algebraMap_restrict k' (RatFunc k') Q'] at hord0
  exact (mul_eq_zero.mp hord0).resolve_left
    (by exact_mod_cast (ramificationIdx_pos (RatFunc k') Q').ne')

omit [Algebra.IsIntegral (RatFunc k) F] [Algebra.IsIntegral (RatFunc k') F'] in
/-- **Places trivial on `F` are unramified over `k'(t)`.** If `F / k(t)` is finite separable and
`F' = F · k'`, then at any place `Q'` of `F'` with `ramificationIdx F Q' = 0` every nonzero element
of `F` is a `Q'`-unit, so the minimal polynomial of a primitive element of `F / k(t)` has `Q'`-unit
derivative and `ramificationIdx (RatFunc k') Q' = 1`. -/
theorem ramificationIdx_ratFunc_eq_one_of_ramificationIdx_eq_zero
    [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
    [FiniteDimensional (RatFunc k') F'] (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q' : Place k' F'}
    (h : ramificationIdx F Q' = 0) :
    ramificationIdx (RatFunc k') Q' = 1 := by
  let φ : RatFunc k →+* RatFunc k' :=
    RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k k'))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (Polynomial.map_injective _ (algebraMap k k').injective))
  have hφ_comm : (algebraMap (RatFunc k') F').comp φ =
      (algebraMap F F').comp (algebraMap (RatFunc k) F) := by
    refine IsFractionRing.ringHom_ext (A := k[X]) fun p ↦ ?_
    simpa [φ, RatFunc.mapRingHom_algebraMap] using (algebraMap_algebraMap_polynomial hX p).symm
  obtain ⟨z, hz_gen⟩ := Field.exists_primitive_element (RatFunc k) F
  have hne : aeval z (derivative (minpoly (RatFunc k) z)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable (RatFunc k) z).aeval_derivative_ne_zero
      (minpoly.aeval (RatFunc k) z)
  have hder_val :
      Q'.valuation (algebraMap F F' (aeval z (derivative (minpoly (RatFunc k) z)))) = 1 :=
    (Q'.ord_eq_iff_valuation_eq_exp_neg ((_root_.map_ne_zero (algebraMap F F')).mpr hne)).mp
      (ord_algebraMap_eq_zero_of_ramificationIdx_eq_zero h _) |>.trans (by simp)
  exact ramificationIdx_eq_one_of_primitive_of_constantCompositum_eq_top hcomp φ hφ_comm hz_gen
    (fun i ↦ by
      rw [mem_integers_restrict_iff]
      have hcomm := congr($hφ_comm ((minpoly (RatFunc k) z).coeff i))
      dsimp at hcomm
      rw [hcomm, Q'.mem_integers_iff_ord_nonneg,
        ord_algebraMap_eq_zero_of_ramificationIdx_eq_zero h])
    hder_val

end RatFunc

section Fibre

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- Using a function `z ∈ F` with a single pole at `P`, the places of `F' / k'` nontrivial on `F`
and restricting to `P` are exactly the poles of `z` in `F'`, hence form a finite set. -/
theorem finite_setOf_restrictOfRamificationIdxNeZero_eq
    (hF : IsFunctionField k F)
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F k' F' = ⊤) (P : Place k F) :
    {P' : Place k' F' | ∃ h : ramificationIdx F P' ≠ 0,
      P'.restrictOfRamificationIdxNeZero k h = P}.Finite := by
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top_of_linearDisjoint H hcomp
  obtain ⟨z, hP, hQ⟩ := exists_ord_neg_and_forall_ne_ord_nonneg hF P
  have hz0 : z ≠ 0 := by rintro rfl; simp at hP
  have hz : algebraMap F F' z ≠ 0 := (_root_.map_ne_zero _).mpr hz0
  refine ((Divisor.poles hF' (Units.mk0 _ hz)).support.finite_toSet).subset fun P' ⟨h, hP'⟩ ↦ ?_
  rw [Finset.mem_coe, AlgebraicGeometry.WeilDivisor.mem_support_iff, Divisor.coeff_poles,
    Units.val_mk0, ord_algebraMap_restrictOfRamificationIdxNeZero (k := k) P' h, hP']
  have hpos : (0 : ℤ) < ramificationIdx F P' := by exact_mod_cast Nat.pos_of_ne_zero h
  have hneg : (ramificationIdx F P' : ℤ) * P.ord z < 0 := mul_neg_of_pos_of_neg hpos hP
  omega

/-- **Degree sum over a place in an arbitrary linearly disjoint constant extension**: over a
perfect base field `k`, the degrees of the places of `F' / k'` nontrivial on `F` and restricting
to `P` add up to `deg P`. -/
theorem finsum_degree_restrictOfRamificationIdxNeZero_eq_degree [PerfectField k]
    (hF : IsFunctionField k F)
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F k' F' = ⊤) (P : Place k F) :
    ∑ᶠ P' ∈ {P' : Place k' F' | ∃ h : ramificationIdx F P' ≠ 0,
      P'.restrictOfRamificationIdxNeZero k h = P}, P'.degree = P.degree := by
  classical
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top_of_linearDisjoint H hcomp
  have hfin := finite_setOf_restrictOfRamificationIdxNeZero_eq hF H hcomp P
  obtain ⟨z, hP, hQ⟩ := exists_ord_neg_and_forall_ne_ord_nonneg hF P
  obtain ⟨n, hn⟩ : ∃ n : ℕ, P.ord z = -(n : ℤ) := ⟨(-P.ord z).toNat, by omega⟩
  have hn0 : n ≠ 0 := by omega
  have hz0 : z ≠ 0 := by rintro rfl; simp at hP
  have hz : algebraMap F F' z ≠ 0 := (_root_.map_ne_zero _).mpr hz0
  have hzk : Transcendental k z := P.transcendental_of_ord_ne_zero hP.ne
  have hzk' : Transcendental k' (algebraMap F F' z) := H.transcendental_algebraMap hzk
  have : FiniteDimensional k⟮z⟯ F := hF.finiteDimensional_adjoin hzk
  have hpoles' : Divisor.poles hF' (Units.mk0 _ hz) =
      (n : ℤ) • AlgebraicGeometry.WeilDivisor.ofFinset hfin.toFinset := by
    ext P'
    rw [Divisor.coeff_poles, Units.val_mk0, AlgebraicGeometry.WeilDivisor.coeff_zsmul,
      AlgebraicGeometry.WeilDivisor.coeff_ofFinset]
    by_cases hmem : ∃ h : ramificationIdx F P' ≠ 0, P'.restrictOfRamificationIdxNeZero k h = P
    · rcases hmem with ⟨h, hP'⟩
      have hmem' : P' ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨h, hP'⟩
      rw [ite_eq_left hmem', mul_one, ord_algebraMap_restrictOfRamificationIdxNeZero (k := k) P' h,
        ramificationIdx_eq_one_of_ramificationIdx_ne_zero hF hcomp h, hP', hn, Nat.cast_one,
        one_mul]
      omega
    · have hnot : P' ∉ hfin.toFinset := fun hm ↦ hmem (hfin.mem_toFinset.mp hm)
      rw [ite_eq_right hnot, mul_zero]
      rcases eq_or_ne (ramificationIdx F P') 0 with h0 | hne
      · have hord0 := ord_algebraMap_eq_zero_of_ramificationIdx_eq_zero h0 z
        omega
      · have hneP : P'.restrictOfRamificationIdxNeZero k hne ≠ P := fun heq ↦ hmem ⟨hne, heq⟩
        have hnonneg := mul_nonneg (Nat.cast_nonneg (ramificationIdx F P')) (hQ _ hneP)
        rw [← ord_algebraMap_restrictOfRamificationIdxNeZero (k := k) P' hne] at hnonneg
        omega
  have hdeg := Divisor.degree_poles hF' (Units.mk0 _ hz) hzk'
  rw [hpoles', Divisor.degree_zsmul, AlgebraicGeometry.WeilDivisor.ofFinset_eq_sum, map_sum,
    Units.val_mk0, finrank_over_adjoin_simple_eq_of_linearDisjoint H hcomp z,
    finrank_adjoin_eq_mul_degree_of_ord_eq_neg hF hn hQ] at hdeg
  simp only [Divisor.degree_ofPoint] at hdeg
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  push_cast at hdeg
  exact_mod_cast mul_left_cancel₀ (by exact_mod_cast hn0 : (n : ℤ) ≠ 0) hdeg

/-- **Every place of `F / k` lifts to a place of `F' / k'` nontrivial on `F`** in an arbitrary
linearly disjoint constant extension over a perfect base field. -/
theorem exists_restrictOfRamificationIdxNeZero_eq [PerfectField k]
    (hF : IsFunctionField k F)
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F k' F' = ⊤) (P : Place k F) :
    ∃ (P' : Place k' F') (h : ramificationIdx F P' ≠ 0),
      P'.restrictOfRamificationIdxNeZero k h = P := by
  by_contra! hall
  have hempty : {P' : Place k' F' | ∃ h : ramificationIdx F P' ≠ 0,
      P'.restrictOfRamificationIdxNeZero k h = P} = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun P' ⟨h, hP'⟩ ↦ hall P' h hP'
  have hsum := finsum_degree_restrictOfRamificationIdxNeZero_eq_degree hF H hcomp P
  rw [hempty, finsum_mem_empty] at hsum
  have hpos := P.one_le_degree_of_isFunctionField hF
  omega

/-- Over an algebraically closed enlarged constant field `k'`, a place `P` of `F / k` has exactly
`deg P` places of `F' / k'` nontrivial on `F` above it. -/
theorem ncard_setOf_restrictOfRamificationIdxNeZero_eq_of_isAlgClosed
    [PerfectField k] [IsAlgClosed k'] (hF : IsFunctionField k F)
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F k' F' = ⊤) (P : Place k F) :
    {P' : Place k' F' | ∃ h : ramificationIdx F P' ≠ 0,
      P'.restrictOfRamificationIdxNeZero k h = P}.ncard = P.degree := by
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top_of_linearDisjoint H hcomp
  have hfin := finite_setOf_restrictOfRamificationIdxNeZero_eq hF H hcomp P
  rw [← finsum_degree_restrictOfRamificationIdxNeZero_eq_degree hF H hcomp P,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_ones]
  exact Finset.sum_congr rfl fun P' _ ↦
    (P'.degree_eq_one_of_isAlgClosed_of_isFunctionField hF').symm

end Fibre

end Place

end TauCeti
