/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.RingTheory.Valuation.Basic
public import TauCeti.GroupTheory.BruhatTits.Valuation
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Pi
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced
import TauCeti.Algebra.Algebra.Pi

/-!
# The valued root datum of `SL₂`

This file constructs the basic example of Bruhat–Tits theory: the root datum of type `A₁` in
`SL₂(K)` for a field `K`, and, for a nontrivial real valuation `ω` of `K`, its standard
valuation. It is the rank-one case on which the apartment, the affine roots and the tree of
`SL₂` over a local field are modelled.

The root system is the pinned root datum of `SL₂`,
`TauCeti.DynkinType.typeASimplyConnectedRootDatum 1`, base changed to a commutative ring `R` of
characteristic zero (an ordered field, for the root datum). Its roots are indexed by the ordered
pairs `(a, b)` of distinct elements of `Fin 2`. Both the root and the coroot spaces are
`Fin 1 → R`, in which the root `e_a - e_b` is `±2` and its coroot is `±1`, with the sign `+` for
`a = 0`. The datum `TauCeti.BruhatTits.RootDatum.sl2` has

* `T` the diagonal torus of `SL₂(K)`;
* `U (e_a - e_b)` the transvections `1 + c E_{a b}`, so that `e₀ - e₁` gives the upper and
  `e₁ - e₀` the lower unipotent subgroup;
* both reflection cosets equal to the antidiagonal matrices, the coset `T S` of the Weyl element
  `S = !![0, -1; 1, 0]`;
* the positive vector the coroot of `e₀ - e₁`, making the upper unipotent subgroup positive.

The axiom (DR4) comes from the factorization
`1 + c E_{b a} = (1 + c⁻¹ E_{a b}) m (1 + c⁻¹ E_{a b})` with `m` antidiagonal, and (DR5) from the
fact that an antidiagonal `m` conjugates `1 + c E_{a b}` to `1 - m_{b a}² c E_{b a}`.

The standard valuation `TauCeti.BruhatTits.Valuation.sl2` gives `1 + c E_{a b}` the value `ω c`.
Its (V5) is the computation that `(1 + d E_{b a}) (1 + c E_{a b}) (1 + e E_{b a})` is antidiagonal
only if `d c = -1`, so that `ω d = -ω c`. It is compatible with the valuation map of the diagonal
torus, `diag(t, t⁻¹) ↦ -ω t` (`TauCeti.BruhatTits.Valuation.isCompatible_sl2`), its value sets
are `ω (Kˣ)`, and the nontriviality of `ω` is necessary
(`TauCeti.BruhatTits.Valuation.exists_ne_zero_and_map_ne_zero_of_sl2_apply_eq`).

## Main definitions

* `TauCeti.BruhatTits.sl2RootPairing`: the root pairing of type `A₁` over `R`.
* `TauCeti.BruhatTits.RootDatum.sl2`: the root datum of type `A₁` in `SL₂(K)`.
* `TauCeti.BruhatTits.Valuation.sl2`: its standard valuation for a real valuation `ω` of `K`.
* `TauCeti.BruhatTits.sl2TorusValuationMap`: the valuation map `diag(t, t⁻¹) ↦ -ω t` of the
  diagonal torus.

## Main results

* `TauCeti.BruhatTits.sl2RootPairing_root`, `sl2RootPairing_coroot` and `sl2RootPairing_pairing`:
  the roots `±2`, coroots `±1` and Cartan integers `±2`; the pairing is crystallographic, reduced
  over a domain, and a root system when `2` is invertible.
* `TauCeti.BruhatTits.RootDatum.isGenerating_sl2`: the root datum of `SL₂(K)` is generating.
* `TauCeti.BruhatTits.RootDatum.sl2_positiveSubgroup`, `sl2_negativeSubgroup` and
  `mem_sl2_weylNormalizer_iff`: `U⁺` and `U⁻` are the upper and lower unipotent subgroups, and `N`
  consists of the diagonal and antidiagonal matrices.
* `TauCeti.BruhatTits.Valuation.isCompatible_sl2`: the standard valuation is compatible with the
  valuation map of the diagonal torus.
* `TauCeti.BruhatTits.Valuation.valueSet_sl2`: both value sets are `ω (Kˣ)`.
* `TauCeti.BruhatTits.sl2TorusValuationMap_mul` and `sl2TorusValuationMap_inv`: the valuation map
  of the diagonal torus is a homomorphism.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. I*, Publ. Math. IHÉS 41 (1972),
  6.1.3 a), p. 109, and 6.2.3 a), pp. 117–118.
-/

public section

open _root_.Matrix _root_.Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise commutatorElement

namespace TauCeti.BruhatTits

open DynkinType

/-! ### Computations in `SL₂` -/

namespace SL2

variable {K : Type*} [Field K] {a b : Fin 2}

private lemma fin_two_cases (hab : a ≠ b) : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  fin_cases a <;> fin_cases b <;> simp_all

/-- Conjugation by an antidiagonal element exchanges the two root subgroups. -/
private lemma antidiagonal_mul_transvection (hab : a ≠ b) {m : SL(2, K)}
    (h0 : (m : Matrix (Fin 2) (Fin 2) K) 0 0 = 0) (h1 : (m : Matrix (Fin 2) (Fin 2) K) 1 1 = 0)
    (c : K) :
    m * transvection hab c =
      transvection hab.symm (-((m : Matrix (Fin 2) (Fin 2) K) b a) ^ 2 * c) * m := by
  have hdet := fin_two_mul_sub_mul_eq_one m
  rw [h0, h1] at hdet
  rcases fin_two_cases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, coe_mul, transvection_coe,
      Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_two, one_apply_eq, one_apply_ne,
      single_apply_same, single_apply_of_ne, ne_eq, one_ne_zero, zero_ne_one, not_false_eq_true,
      and_true, and_false, false_and, h0, h1, mul_one, mul_zero, one_mul, zero_mul, add_zero,
      zero_add, neg_mul] <;>
    first
    | linear_combination (-(c * (m : Matrix (Fin 2) (Fin 2) K) 1 0)) * hdet
    | linear_combination (-(c * (m : Matrix (Fin 2) (Fin 2) K) 0 1)) * hdet

/-- Conjugation by a diagonal element `diag(t, t⁻¹)` scales the root subgroup of `e_a - e_b` by
the square of the `a`-th diagonal entry. -/
private lemma diagonal_mul_transvection (hab : a ≠ b) {z : SL(2, K)}
    (h0 : (z : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) (h1 : (z : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (c : K) :
    z * transvection hab c =
      transvection hab ((z : Matrix (Fin 2) (Fin 2) K) a a ^ 2 * c) * z := by
  have hdet := fin_two_mul_sub_mul_eq_one z
  rw [h0, h1] at hdet
  rcases fin_two_cases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, coe_mul, transvection_coe,
      Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_two, one_apply_eq, one_apply_ne,
      single_apply_same, single_apply_of_ne, ne_eq, one_ne_zero, zero_ne_one, not_false_eq_true,
      and_true, and_false, false_and, h0, h1, mul_one, mul_zero, one_mul, zero_mul, add_zero,
      zero_add] <;>
    first
    | linear_combination (-(c * (z : Matrix (Fin 2) (Fin 2) K) 0 0)) * hdet
    | linear_combination (-(c * (z : Matrix (Fin 2) (Fin 2) K) 1 1)) * hdet

/-- The Bruhat factorization in rank one: for `c ≠ 0`, the product
`(1 - c⁻¹ E_{a b}) (1 + c E_{b a}) (1 - c⁻¹ E_{a b})` is antidiagonal. -/
private lemma bruhat_apply (hab : a ≠ b) {c : K} (hc : c ≠ 0) :
    ((transvection hab (-c⁻¹) * transvection hab.symm c * transvection hab (-c⁻¹) :
      SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 ∧
    ((transvection hab (-c⁻¹) * transvection hab.symm c * transvection hab (-c⁻¹) :
      SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by
  rcases fin_two_cases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [transvection_coe, Matrix.mul_apply, Fin.sum_univ_two, hc]

private lemma transvection_mul_mul_apply (hab : a ≠ b) (c d e : K) :
    ((transvection hab.symm d * transvection hab c * transvection hab.symm e : SL(2, K)) :
      Matrix (Fin 2) (Fin 2) K) b b = 1 + d * c := by
  rcases fin_two_cases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [transvection_coe, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [transvection_coe, Matrix.mul_apply, Fin.sum_univ_two]

/-- The antidiagonal elements of `SL₂(K)` form the right coset `T S` of the diagonal torus. -/
private lemma mem_reflectionCoset_iff {g : SL(2, K)} :
    ((g : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0) ↔
      g ∈ MulOpposite.op ((ModularGroup.S : SL(2, ℤ)) : SL(2, K)) •
        (SpecialLinearGroup.diagonalTorus K 2 : Set SL(2, K)) := by
  rw [Set.mem_smul_set]
  have hS := TauCeti.Matrix.SpecialLinearGroup.coe_modularGroup_S (R := K)
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨g * ((ModularGroup.S : SL(2, ℤ)) : SL(2, K))⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, _root_.Matrix.SpecialLinearGroup.mem_diagonalTorus_iff,
      _root_.Matrix.SpecialLinearGroup.coe_mul, _root_.Matrix.SpecialLinearGroup.coe_inv, hS,
      adjugate_fin_two]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.mul_apply, Fin.sum_univ_two]
  · rintro ⟨t, ht, rfl⟩
    rw [SetLike.mem_coe, _root_.Matrix.SpecialLinearGroup.mem_diagonalTorus_iff] at ht
    have h01 : (t : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := ht (by decide)
    have h10 : (t : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := ht (by decide)
    simp [MulOpposite.smul_eq_mul_unop, Matrix.mul_apply, Fin.sum_univ_two, hS, h01, h10]

private lemma transvection_mem_mul_mul (hab : a ≠ b) {c : K} (hc : c ≠ 0) :
    transvection hab.symm c ∈ ((transvectionHom (A := K) hab).range : Set SL(2, K)) *
      {g : SL(2, K) | (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0} * (transvectionHom (A := K) hab).range := by
  have hx : transvection hab c⁻¹ ∈ (transvectionHom hab).range :=
    ⟨Multiplicative.ofAdd c⁻¹, transvectionHom_apply _ _⟩
  refine Set.mem_mul.mpr ⟨_, Set.mem_mul.mpr ⟨_, hx, _, bruhat_apply hab hc, rfl⟩, _, hx, ?_⟩
  rw [← transvection_inv]
  group

private lemma conjAct_smul_range_transvectionHom (hab : a ≠ b) {m : SL(2, K)}
    (h0 : (m : Matrix (Fin 2) (Fin 2) K) 0 0 = 0) (h1 : (m : Matrix (Fin 2) (Fin 2) K) 1 1 = 0) :
    ConjAct.toConjAct m • (transvectionHom (A := K) hab).range =
      (transvectionHom hab.symm).range := by
  have hdet := fin_two_mul_sub_mul_eq_one m
  rw [h0, h1] at hdet
  have hm : (m : Matrix (Fin 2) (Fin 2) K) b a ≠ 0 := by
    rcases fin_two_cases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rintro h <;> simp [h] at hdet
  have key (c : K) : m⁻¹ * transvection hab.symm (-((m : Matrix (Fin 2) (Fin 2) K) b a) ^ 2 * c) *
      m = transvection hab c := by
    rw [mul_assoc, inv_mul_eq_iff_eq_mul, antidiagonal_mul_transvection hab h0 h1]
  ext g
  rw [Subgroup.mem_conjAct_smul_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨Multiplicative.ofAdd (-((m : Matrix (Fin 2) (Fin 2) K) b a) ^ 2 * c.toAdd), ?_⟩
    rw [transvectionHom_apply] at hc ⊢
    have := key c.toAdd
    rw [hc] at this
    simpa using this
  · rintro ⟨d, rfl⟩
    refine ⟨Multiplicative.ofAdd (-d.toAdd / ((m : Matrix (Fin 2) (Fin 2) K) b a) ^ 2), ?_⟩
    rw [transvectionHom_apply, transvectionHom_apply, ← key, toAdd_ofAdd]
    congr 2
    field_simp

/-- The conjugation constant of (V2): conjugation by an antidiagonal `m` sends `1 + d E_{b a}` to
an element of the root subgroup of `e_a - e_b` whose value is `ω d + 2 ω (m_{a b})`, so `ω d` is
that value plus the constant `-2 ω (m_{a b})`. -/
private lemma exists_apply_transvection_eq_apply_conj_add (ω : AddValuation K (WithTop ℝ))
    (hab : a ≠ b) {m : SL(2, K)} (h0 : (m : Matrix (Fin 2) (Fin 2) K) 0 0 = 0)
    (h1 : (m : Matrix (Fin 2) (Fin 2) K) 1 1 = 0) :
    ∃ c : ℝ, ∀ d : K, ω d =
      ω (((m * transvection hab.symm d * m⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) a b) + c := by
  have hdet := fin_two_mul_sub_mul_eq_one m
  rw [h0, h1] at hdet
  have hm : (m : Matrix (Fin 2) (Fin 2) K) a b ≠ 0 := by
    rcases fin_two_cases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rintro h <;> simp [h] at hdet
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ((ω.ne_top_iff).mpr hm)
  refine ⟨-(2 * r), fun d ↦ ?_⟩
  rw [antidiagonal_mul_transvection hab.symm h0 h1, mul_inv_cancel_right, transvection_apply_same,
    AddValuation.map_mul, AddValuation.map_neg, AddValuation.map_pow, ← hr]
  induction ω d using WithTop.recTopCoe with
  | top => simp
  | coe s =>
    norm_cast
    ring

/-- The computation behind (V5): if `(1 + d E_{b a}) (1 + c E_{a b}) (1 + e E_{b a})` is
antidiagonal, then `d c = -1`, so `ω d = -ω c`. -/
private lemma apply_eq_neg_of_mul_mul_mem (ω : AddValuation K (WithTop ℝ)) (hab : a ≠ b)
    {c d e : K}
    (h : ((transvection hab.symm d * transvection hab c * transvection hab.symm e : SL(2, K)) :
      Matrix (Fin 2) (Fin 2) K) 0 0 = 0 ∧
      ((transvection hab.symm d * transvection hab c * transvection hab.symm e : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K) 1 1 = 0) :
    ω d = -ω c := by
  have hbb : ((transvection hab.symm d * transvection hab c * transvection hab.symm e :
      SL(2, K)) : Matrix (Fin 2) (Fin 2) K) b b = 0 := by
    rcases fin_two_cases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [h.2, h.1]
  rw [transvection_mul_mul_apply] at hbb
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hbb
  rw [show d = -c⁻¹ by field_simp; linear_combination hbb, AddValuation.map_neg,
    AddValuation.map_inv]

/-- The computation behind the compatibility with the torus: conjugation by `diag(t, t⁻¹)`
changes `ω` of the `(a, b)` entry by `2 ω t` if `a = 0` and by `-2 ω t` if `a = 1`. -/
private lemma apply_conj_diagonal (ω : AddValuation K (WithTop ℝ)) (hab : a ≠ b) {z : SL(2, K)}
    (h01 : (z : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) (h10 : (z : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (c : K) :
    ω (((z * transvection hab c * z⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) a b) =
      ω c - (((if a = 0 then 2 else -2) *
        -(ω ((z : Matrix (Fin 2) (Fin 2) K) 0 0)).untop₀ : ℝ) : WithTop ℝ) := by
  have hdet := fin_two_mul_sub_mul_eq_one z
  rw [h01, h10, mul_zero, sub_zero] at hdet
  have hz0 : (z : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hz1 : ω ((z : Matrix (Fin 2) (Fin 2) K) 1 1) = -ω ((z : Matrix (Fin 2) (Fin 2) K) 0 0) := by
    rw [eq_inv_of_mul_eq_one_right hdet, AddValuation.map_inv]
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ((ω.ne_top_iff).mpr hz0)
  rw [diagonal_mul_transvection hab h01 h10, mul_inv_cancel_right, transvection_apply_same,
    AddValuation.map_mul, AddValuation.map_pow, ← hr, WithTop.untop₀_coe]
  rcases fin_two_cases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [← hr]
    induction ω c using WithTop.recTopCoe with
    | top => simp
    | coe s =>
      norm_cast
      simp
      ring
  · rw [hz1, ← hr]
    induction ω c using WithTop.recTopCoe with
    | top => simp
    | coe s =>
      norm_cast
      simp
      ring

end SL2

/-! ### The root pairing of type `A₁` -/

section RootPairing

variable (R : Type*) [CommRing R] [CharZero R]

/-- The root pairing of type `A₁` over `R`: the pinned root datum of `SL₂`, whose two roots
`±(e₀ - e₁)` are indexed by the ordered pairs `(0, 1)` and `(1, 0)`, base changed to `R`. Both
lattices become `Fin 1 → R`; the root `e_a - e_b` is `±2` and its coroot `±1`. -/
noncomputable def sl2RootPairing : RootPairing (Fin (1 * (1 + 1))) R (Fin 1 → R) (Fin 1 → R) :=
  rootPairingBaseChange R (typeASimplyConnectedRootDatum 1)
    toLinearMap_typeASimplyConnectedRootDatum

/-- The root pairing of `SL₂` is the base change of the pinned root datum of `SL₂`. The body of
`sl2RootPairing` is not exposed to importing modules, so use this equation to apply results on
base-changed pairings to it. -/
theorem sl2RootPairing_def :
    sl2RootPairing R = rootPairingBaseChange R (typeASimplyConnectedRootDatum 1)
      toLinearMap_typeASimplyConnectedRootDatum :=
  (rfl)

instance instIsCrystallographicSl2RootPairing : (sl2RootPairing R).IsCrystallographic :=
  isCrystallographic_rootPairingBaseChange ..

instance instIsReducedSl2RootPairing [IsDomain R] : (sl2RootPairing R).IsReduced :=
  isReduced_rootPairingBaseChange R _ _

variable {R}

/-- The pairing of the root pairing of `SL₂` is the dot product of `Fin 1 → R` with itself. -/
@[simp]
theorem sl2RootPairing_toLinearMap (x y : Fin 1 → R) :
    (sl2RootPairing R).toLinearMap x y = x ⬝ᵥ y :=
  toLinearMap_rootPairingBaseChange ..

/-- The reflection permutation of the root pairing of `SL₂` is that of the pinned root datum. -/
@[simp]
theorem sl2RootPairing_reflectionPerm :
    (sl2RootPairing R).reflectionPerm = (typeASimplyConnectedRootDatum 1).reflectionPerm :=
  reflectionPerm_rootPairingBaseChange ..

/-- The root `e_a - e_b` of `SL₂` is `2` if `a = 0`, and `-2` if `a = 1`. -/
@[simp]
theorem sl2RootPairing_root (k : Fin (1 * (1 + 1))) :
    (sl2RootPairing R).root k =
      fun _ ↦ if ((typeAIndexEquiv 1).symm k).val.1 = 0 then 2 else -2 := by
  obtain ⟨p, rfl⟩ := (typeAIndexEquiv 1).surjective k
  have : p = ⟨(0, 1), by decide⟩ ∨ p = ⟨(1, 0), by decide⟩ := by revert p; decide
  ext j
  rcases this with rfl | rfl <;>
    simp only [sl2RootPairing_def, root_rootPairingBaseChange, piAlgebraMap_apply,
      root_typeAIndexEquiv, Equiv.symm_apply_apply, Fin.fin_one_eq_zero j] <;> norm_num

/-- The coroot of `e_a - e_b` of `SL₂` is `1` if `a = 0`, and `-1` if `a = 1`. -/
@[simp]
theorem sl2RootPairing_coroot (k : Fin (1 * (1 + 1))) :
    (sl2RootPairing R).coroot k =
      fun _ ↦ if ((typeAIndexEquiv 1).symm k).val.1 = 0 then 1 else -1 := by
  obtain ⟨p, rfl⟩ := (typeAIndexEquiv 1).surjective k
  have : p = ⟨(0, 1), by decide⟩ ∨ p = ⟨(1, 0), by decide⟩ := by revert p; decide
  ext j
  rcases this with rfl | rfl <;>
    simp only [sl2RootPairing_def, coroot_rootPairingBaseChange, piAlgebraMap_apply,
      coroot_typeAIndexEquiv, Equiv.symm_apply_apply, Fin.fin_one_eq_zero j] <;> norm_num

/-- The root pairing of `SL₂` has Cartan integer `2` between equal roots and `-2` between
opposite ones. -/
@[simp]
theorem sl2RootPairing_pairing (k l : Fin (1 * (1 + 1))) :
    (sl2RootPairing R).pairing k l = if k = l then 2 else -2 := by
  rw [sl2RootPairing_def, pairing_rootPairingBaseChange]
  obtain ⟨p, rfl⟩ := (typeAIndexEquiv 1).surjective k
  obtain ⟨q, rfl⟩ := (typeAIndexEquiv 1).surjective l
  have hp : p = ⟨(0, 1), by decide⟩ ∨ p = ⟨(1, 0), by decide⟩ := by revert p; decide
  have hq : q = ⟨(0, 1), by decide⟩ ∨ q = ⟨(1, 0), by decide⟩ := by revert q; decide
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
    rw [pairing_typeAIndexEquiv] <;> simp [(typeAIndexEquiv 1).injective.eq_iff]

/-- Over a ring in which `2` is invertible, the roots `±2` of `SL₂` span `Fin 1 → R`, so the root
pairing of `SL₂` is a root system. -/
instance instIsRootSystemSl2RootPairing [Invertible (2 : R)] :
    (sl2RootPairing R).IsRootSystem where
  span_root_eq_top := by
    refine eq_top_iff.mpr fun v _ ↦ ?_
    have hv : v =
        (⅟2 * v 0) • (sl2RootPairing R).root (typeAIndexEquiv 1 ⟨(0, 1), by decide⟩) := by
      ext j
      rw [Fin.fin_one_eq_zero j, Pi.smul_apply, sl2RootPairing_root, Equiv.symm_apply_apply]
      simp only [smul_eq_mul, ite_true]
      linear_combination (-v 0) * invOf_mul_self (2 : R)
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  span_coroot_eq_top := by
    rw [sl2RootPairing_def]
    exact span_range_coroot_rootPairingBaseChange_eq_top R _ _
      (corootSpan_typeASimplyConnectedRootDatum_eq_top 1)

/-- The root `e_a - e_b` of `SL₂` takes the value `2 v` at `v` if `a = 0`, and `-2 v` if
`a = 1`. -/
theorem sl2RootPairing_root'_apply (k : Fin (1 * (1 + 1))) (v : Fin 1 → R) :
    (sl2RootPairing R).root' k v =
      (if ((typeAIndexEquiv 1).symm k).val.1 = 0 then 2 else -2) * v 0 := by
  obtain ⟨p, rfl⟩ := (typeAIndexEquiv 1).surjective k
  have : p = ⟨(0, 1), by decide⟩ ∨ p = ⟨(1, 0), by decide⟩ := by revert p; decide
  rcases this with rfl | rfl <;>
    simp only [sl2RootPairing, RootPairing.root', toLinearMap_rootPairingBaseChange,
      root_rootPairingBaseChange, dotProduct, Fin.sum_univ_one, piAlgebraMap_apply,
      root_typeAIndexEquiv, Equiv.symm_apply_apply] <;> norm_num

/-- The reflection in either root of `SL₂` sends each root `e_a - e_b` to `e_b - e_a`. -/
theorem typeAIndexEquiv_symm_sl2RootPairing_reflectionPerm (k l : Fin (1 * (1 + 1))) :
    ((typeAIndexEquiv 1).symm ((sl2RootPairing R).reflectionPerm k l)).val =
      (((typeAIndexEquiv 1).symm l).val.2, ((typeAIndexEquiv 1).symm l).val.1) := by
  obtain ⟨p, rfl⟩ := (typeAIndexEquiv 1).surjective k
  obtain ⟨q, rfl⟩ := (typeAIndexEquiv 1).surjective l
  rw [sl2RootPairing, reflectionPerm_rootPairingBaseChange, typeAIndexEquiv_symm_reflectionPerm,
    Equiv.symm_apply_apply]
  revert p q; decide

/-- Any two roots of `SL₂` are equal or opposite. -/
theorem sl2RootPairing_eq_or_eq_reflectionPerm_self (i j : Fin (1 * (1 + 1))) :
    j = i ∨ j = (sl2RootPairing R).reflectionPerm i i := by
  have h := typeAIndexEquiv_symm_sl2RootPairing_reflectionPerm (R := R) i i
  rw [← (typeAIndexEquiv 1).symm.injective.eq_iff, ← (typeAIndexEquiv 1).symm.injective.eq_iff,
    Subtype.ext_iff, Subtype.ext_iff, h]
  generalize (typeAIndexEquiv 1).symm i = p
  generalize (typeAIndexEquiv 1).symm j = q
  revert p q; decide

end RootPairing

/-! ### The root datum of `SL₂` -/

namespace SL2

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {K : Type*} [Field K]
  {a b : Fin 2}

/-- Only equal roots of `SL₂` satisfy the hypothesis of (DR2) and (V3). -/
private lemma root_ne_neg_smul_iff {i j : Fin (1 * (1 + 1))} :
    (∀ c : R, 0 < c → (sl2RootPairing R).root j ≠ -(c • (sl2RootPairing R).root i)) ↔ j = i := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · refine (sl2RootPairing_eq_or_eq_reflectionPerm_self (R := R) i j).resolve_right fun hj ↦
      h 1 one_pos ?_
    simp [hj]
  · rintro rfl c hc h
    have h' : (1 + c) • (sl2RootPairing R).root j = 0 := by
      linear_combination (norm := module) h
    exact (sl2RootPairing R).ne_zero j ((smul_eq_zero.mp h').resolve_left (by positivity))

/-- The root system of `SL₂` is reduced, so (DR3) and (V4) are vacuous. -/
private lemma root_ne_two_smul (i j : Fin (1 * (1 + 1))) :
    (sl2RootPairing R).root j ≠ (2 : R) • (sl2RootPairing R).root i := fun h ↦ by
  have : HasUniqueDiv (Fin 1 → R) := .of_isTorsionFree R _
  exact (sl2RootPairing R).nsmul_notMem_range_root (n := 2)
    ⟨j, h.trans (ofNat_smul_eq_nsmul R 2 _)⟩

private lemma range_transvectionHom_eq {k : Fin (1 * (1 + 1))} (hab : a ≠ b)
    (hk : ((typeAIndexEquiv 1).symm k).val = (a, b)) :
    (transvectionHom (A := K) ((typeAIndexEquiv 1).symm k).property).range =
      (transvectionHom hab).range := by
  generalize (typeAIndexEquiv 1).symm k = p at hk ⊢
  obtain ⟨⟨a', b'⟩, h⟩ := p
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hk
  rfl

private lemma typeAIndex_one_eq_of_fst_eq_zero (p : TypeAIndex 1) (h : p.val.1 = 0) :
    p.val = (0, 1) := by
  revert p; decide

private lemma typeAIndex_one_eq_of_fst_ne_zero (p : TypeAIndex 1) (h : p.val.1 ≠ 0) :
    p.val = (1, 0) := by
  revert p; decide

/-- The root subgroups of the positive roots of `SL₂` lie in the upper unipotent subgroup. -/
private lemma iSup_pos_le_range_transvectionHom :
    ⨆ (i) (_ : 0 < (sl2RootPairing R).root' i (fun _ ↦ 1)),
      (transvectionHom (A := K) ((typeAIndexEquiv 1).symm i).property).range ≤
        (transvectionHom (A := K) (zero_ne_one : (0 : Fin 2) ≠ 1)).range := by
  refine iSup₂_le fun i hi ↦ (range_transvectionHom_eq _ ?_).le
  rw [sl2RootPairing_root'_apply] at hi
  split_ifs at hi with h
  · exact typeAIndex_one_eq_of_fst_eq_zero _ h
  · norm_num at hi

/-- The root subgroups of the negative roots of `SL₂` lie in the lower unipotent subgroup. -/
private lemma iSup_neg_le_range_transvectionHom :
    ⨆ (i) (_ : (sl2RootPairing R).root' i (fun _ ↦ 1) < 0),
      (transvectionHom (A := K) ((typeAIndexEquiv 1).symm i).property).range ≤
        (transvectionHom (A := K) (one_ne_zero : (1 : Fin 2) ≠ 0)).range := by
  refine iSup₂_le fun i hi ↦ (range_transvectionHom_eq _ ?_).le
  rw [sl2RootPairing_root'_apply] at hi
  split_ifs at hi with h
  · norm_num at hi
  · exact typeAIndex_one_eq_of_fst_ne_zero _ h

/-- The axiom (DR6) for `SL₂`: `U⁺` is the upper and `U⁻` the lower unipotent subgroup, and an
upper triangular element of the lower unipotent subgroup is trivial. -/
private lemma mul_eq_one_of_mem_of_mem {t u : SL(2, K)}
    (ht : t ∈ SpecialLinearGroup.diagonalTorus K 2)
    (hu : u ∈ ⨆ (i) (_ : 0 < (sl2RootPairing R).root' i (fun _ ↦ 1)),
      (transvectionHom (A := K) ((typeAIndexEquiv 1).symm i).property).range)
    (htu : t * u ∈ ⨆ (i) (_ : (sl2RootPairing R).root' i (fun _ ↦ 1) < 0),
      (transvectionHom (A := K) ((typeAIndexEquiv 1).symm i).property).range) :
    t * u = 1 := by
  have hu' := (mem_range_transvectionHom_iff _).mp (iSup_pos_le_range_transvectionHom hu)
  have htu' := (mem_range_transvectionHom_iff _).mp (iSup_neg_le_range_transvectionHom htu)
  have ht' : (t : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 :=
    (_root_.Matrix.SpecialLinearGroup.mem_diagonalTorus_iff.mp ht) (by decide)
  have hu10 : (u : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    rw [← hu']
    simp [transvection_coe]
  rw [← htu', _root_.Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ht',
    hu10, zero_mul, mul_zero, add_zero, transvection_coeff_zero]

end SL2

open SL2 in
/-- The root datum of type `A₁` in `SL₂(K)` ([Bruhat–Tits I], 6.1.3 a)): the diagonal torus, the
upper and lower unipotent subgroups as the root subgroups of `e₀ - e₁` and `e₁ - e₀`, and the
antidiagonal matrices as the common reflection coset of both roots. The positive vector is the
coroot of `e₀ - e₁`, so the upper unipotent subgroup is the positive one. -/
noncomputable def RootDatum.sl2 (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (K : Type*) [Field K] : RootDatum (sl2RootPairing R) SL(2, K) where
  T := SpecialLinearGroup.diagonalTorus K 2
  U k := (transvectionHom ((typeAIndexEquiv 1).symm k).property).range
  reflectionCoset _ :=
    {g | (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0}
  positiveVector _ := 1
  U_ne_bot k := by
    rw [Ne, Subgroup.eq_bot_iff_forall]
    exact fun h ↦ one_ne_zero ((transvection_eq_one_iff ((typeAIndexEquiv 1).symm k).property).mp
      (h _ (MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd 1, transvectionHom_apply _ _⟩)))
  commutator_le i j hij := by
    obtain rfl := root_ne_neg_smul_iff.mp hij
    rw [Subgroup.commutator_self_eq_bot_iff.mpr inferInstance]
    exact bot_le
  le_of_root_eq_two_smul i j h := absurd h (root_ne_two_smul i j)
  ne_of_root_eq_two_smul i j h := absurd h (root_ne_two_smul i j)
  reflectionCoset_eq _ := ⟨_, Set.ext fun _ ↦ mem_reflectionCoset_iff⟩
  bruhat i := by
    obtain ⟨⟨⟨a, b⟩, hab⟩, hp⟩ : ∃ p, (typeAIndexEquiv 1).symm i = p := ⟨_, rfl⟩
    have hi : ((typeAIndexEquiv 1).symm i).val = (a, b) := by rw [hp]
    have hi' : ((typeAIndexEquiv 1).symm ((sl2RootPairing R).reflectionPerm i i)).val = (b, a) := by
      rw [typeAIndexEquiv_symm_sl2RootPairing_reflectionPerm, hi]
    rw [range_transvectionHom_eq hab hi, range_transvectionHom_eq hab.symm hi']
    rintro _ ⟨⟨c, rfl⟩, hc⟩
    rw [transvectionHom_apply] at hc ⊢
    refine transvection_mem_mul_mul hab fun h ↦ hc ?_
    rw [h, transvection_coeff_zero]
    exact Set.mem_singleton 1
  reflection_conjugates i m hm j := by
    obtain ⟨⟨⟨a, b⟩, hab⟩, hp⟩ : ∃ p, (typeAIndexEquiv 1).symm j = p := ⟨_, rfl⟩
    have hj : ((typeAIndexEquiv 1).symm j).val = (a, b) := by rw [hp]
    have hj' : ((typeAIndexEquiv 1).symm ((sl2RootPairing R).reflectionPerm i j)).val = (b, a) := by
      rw [typeAIndexEquiv_symm_sl2RootPairing_reflectionPerm, hj]
    rw [range_transvectionHom_eq hab hj, range_transvectionHom_eq hab.symm hj']
    exact conjAct_smul_range_transvectionHom hab hm.1 hm.2
  positiveVector_regular i := by
    rw [sl2RootPairing_root'_apply]
    split_ifs <;> norm_num
  -- In term mode the elaborator unifies against the uninstantiated field type and times out;
  -- after the binders are introduced the types are syntactically those of the lemma.
  bruhat_separation _ ht _ hu htu := by
    exact mul_eq_one_of_mem_of_mem ht hu htu

namespace RootDatum

variable (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] (K : Type*) [Field K]

/-- The torus of the root datum of `SL₂(K)` is the diagonal torus. -/
@[simp]
theorem sl2_T : (sl2 R K).T = SpecialLinearGroup.diagonalTorus K 2 :=
  (rfl)

/-- The root subgroup of the root of index `k` of `SL₂(K)`. -/
theorem sl2_U (k : Fin (1 * (1 + 1))) :
    (sl2 R K).U k = (transvectionHom ((typeAIndexEquiv 1).symm k).property).range :=
  (rfl)

/-- The root subgroup of the root `e_a - e_b` of `SL₂(K)` consists of the transvections
`1 + c E_{a b}`. -/
@[simp]
theorem sl2_U_typeAIndexEquiv (p : TypeAIndex 1) :
    (sl2 R K).U (typeAIndexEquiv 1 p) = (transvectionHom p.property).range := by
  rw [sl2_U, Equiv.symm_apply_apply]

/-- Both reflection cosets of the root datum of `SL₂(K)` consist of the antidiagonal
matrices. -/
@[simp]
theorem sl2_reflectionCoset (k : Fin (1 * (1 + 1))) :
    (sl2 R K).reflectionCoset k =
      {g : SL(2, K) | (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0} :=
  (rfl)

/-- The positive vector of the root datum of `SL₂(K)` is the coroot of `e₀ - e₁`. -/
@[simp]
theorem sl2_positiveVector : (sl2 R K).positiveVector = fun _ ↦ 1 :=
  (rfl)

variable {R K}

/-- An element lies in the root subgroup of `e_a - e_b` exactly when it is the transvection
`1 + c E_{a b}` by its own `(a, b)` entry `c`. -/
theorem mem_sl2_U_iff {k : Fin (1 * (1 + 1))} {g : SL(2, K)} :
    g ∈ (sl2 R K).U k ↔
      transvection ((typeAIndexEquiv 1).symm k).property
        ((g : Matrix (Fin 2) (Fin 2) K) ((typeAIndexEquiv 1).symm k).val.1
          ((typeAIndexEquiv 1).symm k).val.2) = g :=
  mem_range_transvectionHom_iff _

/-- The transvection `1 + c E_{a b}` lies in the root subgroup of `e_a - e_b`. -/
theorem transvection_mem_sl2_U (p : TypeAIndex 1) (c : K) :
    transvection p.property c ∈ (sl2 R K).U (typeAIndexEquiv 1 p) := by
  rw [sl2_U_typeAIndexEquiv]
  exact ⟨Multiplicative.ofAdd c, transvectionHom_apply _ _⟩

variable (R K)

/-- `SL₂(K)` is generated by its two root subgroups. -/
theorem iSup_sl2_U : ⨆ k, (sl2 R K).U k = ⊤ :=
  eq_top_iff.mpr fun g _ ↦ SL2.transvection_induction (· ∈ ⨆ k, (sl2 R K).U k)
    (fun i j hij c ↦ Subgroup.mem_iSup_of_mem (typeAIndexEquiv 1 ⟨(i, j), hij⟩)
      (transvection_mem_sl2_U _ c))
    (fun _ _ ↦ mul_mem) g

/-- The root datum of `SL₂(K)` is generating. -/
theorem isGenerating_sl2 : (sl2 R K).IsGenerating := by
  rw [isGenerating_iff, iSup_sl2_U, sup_top_eq]

/-- The positive unipotent subgroup of the root datum of `SL₂(K)` is the upper unipotent
subgroup of the transvections `1 + c E_{0 1}`. -/
@[simp]
theorem sl2_positiveSubgroup :
    (sl2 R K).positiveSubgroup = (transvectionHom (zero_ne_one : (0 : Fin 2) ≠ 1)).range := by
  refine le_antisymm (by rw [positiveSubgroup_def]; exact SL2.iSup_pos_le_range_transvectionHom)
    ((sl2_U_typeAIndexEquiv R K ⟨(0, 1), zero_ne_one⟩).symm.le.trans (U_le_positiveSubgroup ?_))
  rw [sl2_positiveVector, sl2RootPairing_root'_apply, Equiv.symm_apply_apply]
  norm_num

/-- The negative unipotent subgroup of the root datum of `SL₂(K)` is the lower unipotent
subgroup of the transvections `1 + c E_{1 0}`. -/
@[simp]
theorem sl2_negativeSubgroup :
    (sl2 R K).negativeSubgroup = (transvectionHom (one_ne_zero : (1 : Fin 2) ≠ 0)).range := by
  refine le_antisymm (by rw [negativeSubgroup_def]; exact SL2.iSup_neg_le_range_transvectionHom)
    ((sl2_U_typeAIndexEquiv R K ⟨(1, 0), one_ne_zero⟩).symm.le.trans (U_le_negativeSubgroup ?_))
  rw [sl2_positiveVector, sl2RootPairing_root'_apply, Equiv.symm_apply_apply]
  norm_num

variable {R K} in
/-- The subgroup `N` of the root datum of `SL₂(K)` consists of the diagonal and the antidiagonal
matrices. -/
theorem mem_sl2_weylNormalizer_iff {g : SL(2, K)} :
    g ∈ (sl2 R K).weylNormalizer ↔
      ((g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) ∨
        ((g : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0) := by
  constructor
  · intro hg
    rw [weylNormalizer_def] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · have hx' := _root_.Matrix.SpecialLinearGroup.mem_diagonalTorus_iff.mp hx
        exact Or.inl ⟨hx' (by decide), hx' (by decide)⟩
      · obtain ⟨_, hx⟩ := Set.mem_iUnion.mp hx
        exact Or.inr hx
    | one => simp
    | mul x y _ _ hx hy =>
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3, h4]
    | inv x _ hx =>
      rw [_root_.Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  · rintro (⟨h1, h2⟩ | h)
    · refine T_le_weylNormalizer (_root_.Matrix.SpecialLinearGroup.mem_diagonalTorus_iff.mpr ?_)
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · exact reflectionCoset_subset_weylNormalizer (typeAIndexEquiv 1 ⟨(0, 1), zero_ne_one⟩) h

end RootDatum

/-! ### The standard valuation -/

namespace SL2

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {K : Type*} [Field K]

/-- An element of the root subgroup of `-a` is a transvection in the transposed position. -/
private lemma transvection_eq_of_mem_U_reflectionPerm_self {i : Fin (1 * (1 + 1))}
    {g : SL(2, K)} (hg : g ∈ (RootDatum.sl2 R K).U ((sl2RootPairing R).reflectionPerm i i)) :
    transvection ((typeAIndexEquiv 1).symm i).property.symm
      ((g : Matrix (Fin 2) (Fin 2) K) ((typeAIndexEquiv 1).symm i).val.2
        ((typeAIndexEquiv 1).symm i).val.1) = g := by
  have key (a b a' b' : Fin 2) (h : a' ≠ b') (h' : a ≠ b) (ha : a' = b) (hb : b' = a)
      (hg : transvection h ((g : Matrix (Fin 2) (Fin 2) K) a' b') = g) :
      transvection h'.symm ((g : Matrix (Fin 2) (Fin 2) K) b a) = g := by
    subst ha hb
    exact hg
  have hr := typeAIndexEquiv_symm_sl2RootPairing_reflectionPerm (R := R) i i
  exact key _ _ _ _ _ ((typeAIndexEquiv 1).symm i).property (congrArg Prod.fst hr)
    (congrArg Prod.snd hr) (RootDatum.mem_sl2_U_iff.mp hg)

/-- The coordinate of the root `-a` is the transposed coordinate of `a`. -/
private lemma apply_reflectionPerm_self (i : Fin (1 * (1 + 1))) (g : SL(2, K)) :
    (g : Matrix (Fin 2) (Fin 2) K)
        ((typeAIndexEquiv 1).symm ((sl2RootPairing R).reflectionPerm i i)).val.1
        ((typeAIndexEquiv 1).symm ((sl2RootPairing R).reflectionPerm i i)).val.2 =
      (g : Matrix (Fin 2) (Fin 2) K) ((typeAIndexEquiv 1).symm i).val.2
        ((typeAIndexEquiv 1).symm i).val.1 := by
  rw [typeAIndexEquiv_symm_sl2RootPairing_reflectionPerm]

/-- The axiom (V0) for the standard valuation of `SL₂`: the values `ω 0 = ⊤`, `ω 1 = 0` and
`ω x ≠ 0, ⊤` are taken on every root subgroup. -/
private lemma three_le_encard_range_sl2 (ω : AddValuation K (WithTop ℝ))
    (hω : ∃ x : K, x ≠ 0 ∧ ω x ≠ 0) (k : Fin (1 * (1 + 1))) :
    3 ≤ (Set.range fun u : (RootDatum.sl2 R K).U k ↦ ω (((u : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
      ((typeAIndexEquiv 1).symm k).val.1 ((typeAIndexEquiv 1).symm k).val.2)).encard := by
  obtain ⟨x, hx0, hx⟩ := hω
  have he (c : K) : ω c ∈ Set.range fun u : (RootDatum.sl2 R K).U k ↦
      ω (((u : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
        ((typeAIndexEquiv 1).symm k).val.1 ((typeAIndexEquiv 1).symm k).val.2) :=
    ⟨⟨transvection ((typeAIndexEquiv 1).symm k).property c,
      ⟨Multiplicative.ofAdd c, transvectionHom_apply _ _⟩⟩, by simp⟩
  calc (3 : ℕ∞) = ({ω 0, ω 1, ω x} : Set (WithTop ℝ)).encard := by
        refine (Set.encard_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩).symm
        · simp
        · rwa [AddValuation.map_zero, ne_comm, Ne, AddValuation.top_iff]
        · rwa [AddValuation.map_one, ne_comm]
    _ ≤ _ := Set.encard_le_encard <| Set.insert_subset_iff.mpr
        ⟨he 0, Set.insert_subset_iff.mpr ⟨he 1, Set.singleton_subset_iff.mpr (he x)⟩⟩

end SL2

section Valuation

variable (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] {K : Type*} [Field K]

open SL2 in
/-- The standard valuation of the root datum of `SL₂(K)` attached to a nontrivial real valuation
`ω` of `K` ([Bruhat–Tits I], 6.2.3 a)): the transvection `1 + c E_{a b}` in the root subgroup of
`e_a - e_b` has value `ω c`. -/
noncomputable def Valuation.sl2 (ω : AddValuation K (WithTop ℝ))
    (hω : ∃ x : K, x ≠ 0 ∧ ω x ≠ 0) : Valuation (RootDatum.sl2 R K) where
  toFun k u := ω (((u : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
    ((typeAIndexEquiv 1).symm k).val.1 ((typeAIndexEquiv 1).symm k).val.2)
  three_le_encard_range := three_le_encard_range_sl2 ω hω
  min_le_apply_mul k u v := by
    rw [Subgroup.coe_mul, mul_apply_of_mem_range_transvectionHom _ u.property v.property]
    exact ω.map_add _ _
  apply_le_apply_inv k u := by
    rw [Subgroup.coe_inv, inv_apply_of_mem_range_transvectionHom _ u.property, AddValuation.map_neg]
  apply_eq_top_iff k u := by
    rw [AddValuation.top_iff, ← OneMemClass.coe_eq_one,
      eq_one_iff_of_mem_range_transvectionHom _ u.property]
  exists_apply_eq_apply_conj_add i m hm := by
    obtain ⟨c, hc⟩ :=
      exists_apply_transvection_eq_apply_conj_add ω ((typeAIndexEquiv 1).symm i).property hm.1 hm.2
    refine ⟨c, fun u _ ↦ ?_⟩
    obtain ⟨g, hg⟩ := u
    dsimp only
    rw [apply_reflectionPerm_self, hc, transvection_eq_of_mem_U_reflectionPerm_self hg]
  commutator_mem i j hij k l u v _ _ := by
    obtain rfl := root_ne_neg_smul_iff.mp hij
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (setLike_mul_comm (s := (transvectionHom ((typeAIndexEquiv 1).symm j).property).range)
        u.property v.property)]
    exact one_mem _
  apply_eq_two_smul i j h := absurd h (root_ne_two_smul i j)
  apply_reflectionPerm_left_eq_neg_of_mul_mul_mem_reflectionCoset i u u' u'' h := by
    obtain ⟨g, hg⟩ := u
    obtain ⟨g', hg'⟩ := u'
    obtain ⟨g'', hg''⟩ := u''
    dsimp only at h ⊢
    rw [← RootDatum.mem_sl2_U_iff.mp hg, ← transvection_eq_of_mem_U_reflectionPerm_self hg',
      ← transvection_eq_of_mem_U_reflectionPerm_self hg''] at h
    rw [apply_reflectionPerm_self]
    exact apply_eq_neg_of_mul_mul_mem ω _ h

namespace Valuation

variable (ω : AddValuation K (WithTop ℝ)) (hω : ∃ x : K, x ≠ 0 ∧ ω x ≠ 0)

/-- The standard valuation of `SL₂(K)` is `ω` of the coordinate of the root subgroup. -/
theorem sl2_apply (k : Fin (1 * (1 + 1))) (u : (RootDatum.sl2 R K).U k) :
    sl2 R ω hω k u = ω (((u : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
      ((typeAIndexEquiv 1).symm k).val.1 ((typeAIndexEquiv 1).symm k).val.2) :=
  (rfl)

/-- The standard valuation of `SL₂(K)` takes the value `ω c` at the transvection `1 + c E_{a b}`
of the root subgroup of `e_a - e_b`. -/
@[simp]
theorem sl2_apply_transvection (p : TypeAIndex 1) (c : K) :
    sl2 R ω hω (typeAIndexEquiv 1 p)
        ⟨transvection p.property c, RootDatum.transvection_mem_sl2_U p c⟩ =
      ω c := by
  rw [sl2_apply]
  simp

/-- An element `1 + c E_{a b}` of the root subgroup of `e_a - e_b` lies in the filtration
subgroup `U (e_a - e_b, r)` exactly when `r ≤ ω c`. -/
theorem transvection_mem_filtration_sl2_iff (p : TypeAIndex 1) (c : K) (r : ℝ) :
    transvection p.property c ∈ (sl2 R ω hω).filtration (typeAIndexEquiv 1 p) r ↔
      (r : WithTop ℝ) ≤ ω c := by
  rw [← sl2_apply_transvection R ω hω p c]
  exact (sl2 R ω hω).coe_mem_filtration_iff ⟨_, RootDatum.transvection_mem_sl2_U p c⟩

/-- The value set of either root of `SL₂(K)` is the value set `ω (Kˣ)` of `ω`. -/
@[simp]
theorem valueSet_sl2 (k : Fin (1 * (1 + 1))) :
    (sl2 R ω hω).valueSet k = {r : ℝ | ∃ x : K, x ≠ 0 ∧ ω x = r} := by
  ext r
  rw [mem_valueSet_iff]
  refine ⟨fun ⟨u, hu⟩ ↦ ⟨_, fun h ↦ ?_, hu⟩, fun ⟨x, _, hx⟩ ↦ ?_⟩
  · rw [sl2_apply, h, AddValuation.map_zero] at hu
    exact WithTop.top_ne_coe hu
  · exact ⟨⟨transvection ((typeAIndexEquiv 1).symm k).property x,
      ⟨Multiplicative.ofAdd x, transvectionHom_apply _ _⟩⟩,
      by rw [sl2_apply, transvection_apply_same, hx]⟩

variable {R} in
/-- The nontriviality hypothesis of `Valuation.sl2` is necessary: if a valuation of the root
datum of `SL₂(K)` takes the value `ω c` at every transvection `1 + c E_{a b}` of one root
subgroup, then `ω` takes a value other than `0` and `⊤`. In particular the trivial valuation of
`K` gives no valuation of this root datum. -/
theorem exists_ne_zero_and_map_ne_zero_of_sl2_apply_eq (φ : Valuation (RootDatum.sl2 R K))
    (k : Fin (1 * (1 + 1)))
    (h : ∀ u : (RootDatum.sl2 R K).U k, φ k u = ω (((u : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
      ((typeAIndexEquiv 1).symm k).val.1 ((typeAIndexEquiv 1).symm k).val.2)) :
    ∃ x : K, x ≠ 0 ∧ ω x ≠ 0 := by
  obtain ⟨r, hr0, hr⟩ := (φ.valueSet_nontrivial k).exists_ne 0
  obtain ⟨u, hu⟩ := φ.mem_valueSet_iff.mp hr0
  rw [h] at hu
  refine ⟨_, (ω.ne_top_iff).mp (hu ▸ WithTop.coe_ne_top), ?_⟩
  rw [hu]
  exact_mod_cast hr

end Valuation

/-- The valuation map of the diagonal torus of `SL₂(K)` for a real valuation `ω` of `K`: it
sends `diag(t, t⁻¹)` to `-ω t`, in the coordinate of the coroot of `e₀ - e₁`. Through
`TauCeti.BruhatTits.Valuation.IsCompatible`, `diag(t, t⁻¹)` acts on the apartment by this
translation. -/
noncomputable def sl2TorusValuationMap (ω : AddValuation K (WithTop ℝ)) :
    (RootDatum.sl2 ℝ K).T → (Fin 1 → ℝ) :=
  fun z _ ↦ -(ω (((z : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0)).untop₀

/-- The valuation map of the diagonal torus sends `diag(t, t⁻¹)` to `-ω t`. -/
@[simp]
theorem sl2TorusValuationMap_apply (ω : AddValuation K (WithTop ℝ)) (z : (RootDatum.sl2 ℝ K).T)
    (j : Fin 1) :
    sl2TorusValuationMap ω z j = -(ω (((z : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0)).untop₀ :=
  (rfl)

/-- The first diagonal entry of an element of the diagonal torus of `SL₂(K)` is nonzero. -/
private lemma SL2.apply_zero_zero_ne_zero_of_mem {z : SL(2, K)}
    (hz : z ∈ SpecialLinearGroup.diagonalTorus K 2) :
    (z : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
  have hz' := _root_.Matrix.SpecialLinearGroup.mem_diagonalTorus_iff.mp hz
  have hdet := fin_two_mul_sub_mul_eq_one z
  rw [hz' (by decide : (1 : Fin 2) ≠ 0), mul_zero, sub_zero] at hdet
  exact left_ne_zero_of_mul_eq_one hdet

/-- Read in `WithTop ℝ`, the valuation map of the diagonal torus sends `diag(t, t⁻¹)` to
`-ω t`. -/
theorem coe_sl2TorusValuationMap_apply (ω : AddValuation K (WithTop ℝ))
    (z : (RootDatum.sl2 ℝ K).T) (j : Fin 1) :
    (sl2TorusValuationMap ω z j : WithTop ℝ) =
      -ω (((z : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) := by
  rw [sl2TorusValuationMap_apply, WithTop.LinearOrderedAddCommGroup.coe_neg,
    WithTop.coe_untop₀_of_ne_top
      ((ω.ne_top_iff).mpr (SL2.apply_zero_zero_ne_zero_of_mem z.property))]

/-- The valuation map of the diagonal torus sends `1` to `0`. -/
@[simp]
theorem sl2TorusValuationMap_one (ω : AddValuation K (WithTop ℝ)) :
    sl2TorusValuationMap ω 1 = 0 := by
  ext j
  simp

/-- The valuation map of the diagonal torus is additive. -/
@[simp]
theorem sl2TorusValuationMap_mul (ω : AddValuation K (WithTop ℝ)) (z w : (RootDatum.sl2 ℝ K).T) :
    sl2TorusValuationMap ω (z * w) = sl2TorusValuationMap ω z + sl2TorusValuationMap ω w := by
  ext j
  have hz := _root_.Matrix.SpecialLinearGroup.mem_diagonalTorus_iff.mp z.property
  have h : (((z * w : (RootDatum.sl2 ℝ K).T) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      ((z : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 *
        ((w : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    rw [Subgroup.coe_mul, _root_.Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hz (by decide : (0 : Fin 2) ≠ 1), zero_mul, add_zero]
  rw [Pi.add_apply, sl2TorusValuationMap_apply, sl2TorusValuationMap_apply,
    sl2TorusValuationMap_apply, h, AddValuation.map_mul,
    WithTop.untop₀_add ((ω.ne_top_iff).mpr (SL2.apply_zero_zero_ne_zero_of_mem z.property))
      ((ω.ne_top_iff).mpr (SL2.apply_zero_zero_ne_zero_of_mem w.property)), neg_add]

/-- The valuation map of the diagonal torus sends inverses to negatives. -/
@[simp]
theorem sl2TorusValuationMap_inv (ω : AddValuation K (WithTop ℝ)) (z : (RootDatum.sl2 ℝ K).T) :
    sl2TorusValuationMap ω z⁻¹ = -sl2TorusValuationMap ω z := by
  ext j
  have hz := _root_.Matrix.SpecialLinearGroup.mem_diagonalTorus_iff.mp z.property
  have hdet := fin_two_mul_sub_mul_eq_one (z : SL(2, K))
  rw [hz (by decide : (1 : Fin 2) ≠ 0), mul_zero, sub_zero] at hdet
  have hinv : (((z⁻¹ : (RootDatum.sl2 ℝ K).T) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      ((z : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    simp
  rw [Pi.neg_apply, sl2TorusValuationMap_apply, sl2TorusValuationMap_apply, hinv,
    eq_inv_of_mul_eq_one_right hdet, AddValuation.map_inv, WithTop.untop₀_neg]

/-- The standard valuation of `SL₂(K)` is compatible with the valuation map of the diagonal
torus: conjugation by `diag(t, t⁻¹)` raises the values on the root subgroup of `e₀ - e₁` by
`2 ω t` and lowers those on the root subgroup of `e₁ - e₀` by `2 ω t`. -/
theorem Valuation.isCompatible_sl2 (ω : AddValuation K (WithTop ℝ))
    (hω : ∃ x : K, x ≠ 0 ∧ ω x ≠ 0) :
    (Valuation.sl2 ℝ ω hω).IsCompatible (sl2TorusValuationMap ω) := by
  rw [Valuation.isCompatible_iff]
  rintro i ⟨z, hz⟩ ⟨g, hg⟩
  rw [RootDatum.sl2_T, _root_.Matrix.SpecialLinearGroup.mem_diagonalTorus_iff] at hz
  rw [Valuation.sl2_apply, Valuation.sl2_apply, sl2RootPairing_root'_apply,
    sl2TorusValuationMap_apply]
  dsimp only
  rw [← RootDatum.mem_sl2_U_iff.mp hg,
    SL2.apply_conj_diagonal ω _ (hz (by decide)) (hz (by decide)), transvection_apply_same]

end Valuation

end TauCeti.BruhatTits
