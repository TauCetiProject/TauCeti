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
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A.RankOne
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Order.Interval.Finite

/-!
# The valued root datum of `SL₂`

This file constructs the basic example of Bruhat–Tits theory: the root datum of type `A₁` in
`SL₂(K)` for a field `K`, and, for a nontrivial real valuation `ω` of `K`, its standard
valuation. It is the rank-one case on which the apartment, the affine roots and the tree of
`SL₂` over a local field are modelled.

The root system is the root pairing `TauCeti.DynkinType.sl2RootPairing R` of type `A₁` over an
ordered field `R`, the pinned root datum of `SL₂` base changed to `R`. Its roots are indexed by
the ordered pairs `(a, b)` of distinct elements of `Fin 2`. Both the root and the coroot spaces
are `Fin 1 → R`, in which the root `e_a - e_b` is `±2` and its coroot is `±1`, with the sign `+`
for `a = 0`. The datum `TauCeti.BruhatTits.RootDatum.sl2` has

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
(`TauCeti.BruhatTits.Valuation.exists_ne_zero_and_map_ne_zero_of_sl2_apply_eq`). It is discrete
exactly when `ω` is, that is, when the positive values of `ω` are bounded away from `0`
(`TauCeti.BruhatTits.Valuation.isDiscrete_sl2_iff`): for instance when `ω` takes integer values on
`Kˣ`, but not when every rational number is a value of `ω`.

## Main definitions

* `TauCeti.BruhatTits.RootDatum.sl2`: the root datum of type `A₁` in `SL₂(K)`.
* `TauCeti.BruhatTits.Valuation.sl2`: its standard valuation for a real valuation `ω` of `K`.
* `TauCeti.BruhatTits.sl2TorusValuationMap`: the valuation map `diag(t, t⁻¹) ↦ -ω t` of the
  diagonal torus.

## Main results

* `TauCeti.BruhatTits.RootDatum.isGenerating_sl2`: the root datum of `SL₂(K)` is generating.
* `TauCeti.BruhatTits.RootDatum.sl2_positiveSubgroup`, `sl2_negativeSubgroup` and
  `mem_sl2_weylNormalizer_iff`: `U⁺` and `U⁻` are the upper and lower unipotent subgroups, and `N`
  consists of the diagonal and antidiagonal matrices.
* `TauCeti.BruhatTits.Valuation.isCompatible_sl2`: the standard valuation is compatible with the
  valuation map of the diagonal torus.
* `TauCeti.BruhatTits.Valuation.valueSet_sl2`: both value sets are `ω (Kˣ)`.
* `TauCeti.BruhatTits.Valuation.isDiscrete_sl2_iff`: the standard valuation is discrete if and
  only if the positive values of `ω` are bounded away from `0`.
* `TauCeti.BruhatTits.sl2TorusValuationMap_mul` and `sl2TorusValuationMap_inv`: the valuation map
  of the diagonal torus is a homomorphism.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. I*, Publ. Math. IHÉS 41 (1972),
  6.1.3 a), p. 109, 6.2.3 a), pp. 117–118, and Définition 6.2.21, p. 127.
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
  rw [transvection_mul_transvection_mul_transvection_apply_self] at hbb
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hbb
  rw [show d = -c⁻¹ by field_simp; linear_combination hbb, AddValuation.map_neg,
    AddValuation.map_inv]

/-- The computation behind the compatibility with the torus: conjugation by `diag(t, t⁻¹)`
changes `ω` of the `(a, b)` entry by `2 ω t` if `a = 0` and by `-2 ω t` if `a = 1`. -/
private lemma apply_conj_diagonal (ω : AddValuation K (WithTop ℝ)) (hab : a ≠ b) {z : SL(2, K)}
    (hz : (z : Matrix (Fin 2) (Fin 2) K).IsDiag) (c : K) :
    ω (((z * transvection hab c * z⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) a b) =
      ω c - (((if a = 0 then 2 else -2) *
        -(ω ((z : Matrix (Fin 2) (Fin 2) K) 0 0)).untop₀ : ℝ) : WithTop ℝ) := by
  have hdet := fin_two_mul_sub_mul_eq_one z
  rw [hz (by decide : (0 : Fin 2) ≠ 1), zero_mul, sub_zero] at hdet
  obtain ⟨r, hr⟩ :=
    WithTop.ne_top_iff_exists.mp ((ω.ne_top_iff).mpr (left_ne_zero_of_mul_eq_one hdet))
  have hz1 : ω ((z : Matrix (Fin 2) (Fin 2) K) 1 1) = ((-r : ℝ) : WithTop ℝ) := by
    rw [eq_inv_of_mul_eq_one_right hdet, AddValuation.map_inv, ← hr,
      WithTop.LinearOrderedAddCommGroup.coe_neg]
  -- Since `(z⁻¹)_{b b} = z_{a a}`, the factor `z_{a a} (z⁻¹)_{b b}` by which conjugation
  -- rescales the parameter has value `2 ω (z_{a a})`, that is `±2 r`.
  have hs : ω ((z : Matrix (Fin 2) (Fin 2) K) a a) +
      ω (((z⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) b b) =
        (((if a = 0 then 2 else -2) * r : ℝ) : WithTop ℝ) := by
    rw [_root_.Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
    rcases fin_two_cases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
        hz1, ← hr, Fin.isValue, ↓reduceIte, one_ne_zero] <;> rw [← WithTop.coe_add] <;>
      congr 1 <;> ring
  rw [diagonal_mul_transvection hab hz, mul_inv_cancel_right, transvection_apply_same,
    AddValuation.map_mul, AddValuation.map_mul, add_right_comm, hs, ← hr, WithTop.untop₀_coe]
  induction ω c using WithTop.recTopCoe with
  | top => simp
  | coe s =>
    norm_cast
    ring

end SL2

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

/-- The root subgroup of a reflected root `s_i j` of `SL₂` consists of the transvections in the
position transposed to that of `j`. -/
private lemma range_transvectionHom_reflectionPerm (i j : Fin (1 * (1 + 1))) :
    (transvectionHom (A := K)
        ((typeAIndexEquiv 1).symm ((sl2RootPairing R).reflectionPerm i j)).property).range =
      (transvectionHom ((typeAIndexEquiv 1).symm j).property.symm).range :=
  range_transvectionHom_eq _ (typeAIndexEquiv_symm_sl2RootPairing_reflectionPerm i j)

/-- The root subgroups of the positive roots of `SL₂` lie in the upper unipotent subgroup. -/
private lemma iSup_pos_le_range_transvectionHom :
    ⨆ (i) (_ : 0 < (sl2RootPairing R).root' i (fun _ ↦ 1)),
      (transvectionHom (A := K) ((typeAIndexEquiv 1).symm i).property).range ≤
        (transvectionHom (A := K) (zero_ne_one : (0 : Fin 2) ≠ 1)).range := by
  refine iSup₂_le fun i hi ↦ (range_transvectionHom_eq _ ?_).le
  rw [sl2RootPairing_root'_apply] at hi
  rcases typeAIndex_one_eq_or_eq ((typeAIndexEquiv 1).symm i) with h | h
  · rw [h]
  · rw [h] at hi
    norm_num at hi

/-- The root subgroups of the negative roots of `SL₂` lie in the lower unipotent subgroup. -/
private lemma iSup_neg_le_range_transvectionHom :
    ⨆ (i) (_ : (sl2RootPairing R).root' i (fun _ ↦ 1) < 0),
      (transvectionHom (A := K) ((typeAIndexEquiv 1).symm i).property).range ≤
        (transvectionHom (A := K) (one_ne_zero : (1 : Fin 2) ≠ 0)).range := by
  refine iSup₂_le fun i hi ↦ (range_transvectionHom_eq _ ?_).le
  rw [sl2RootPairing_root'_apply] at hi
  rcases typeAIndex_one_eq_or_eq ((typeAIndexEquiv 1).symm i) with h | h
  · rw [h] at hi
    norm_num at hi
  · rw [h]

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
  reflectionCoset_eq _ :=
    ⟨_, Set.ext fun _ ↦
      TauCeti.Matrix.SpecialLinearGroup.mem_op_modularGroup_S_smul_diagonalTorus_iff.symm⟩
  bruhat i := by
    rw [range_transvectionHom_reflectionPerm]
    rintro _ ⟨⟨c, rfl⟩, hc⟩
    rw [transvectionHom_apply] at hc ⊢
    refine transvection_mem_range_mul_antidiagonal_mul_range _ fun h ↦ hc ?_
    rw [h, transvection_coeff_zero]
    exact Set.mem_singleton 1
  reflection_conjugates i m hm j := by
    rw [range_transvectionHom_reflectionPerm]
    exact conjAct_smul_range_transvectionHom_of_antidiagonal _ hm.1 hm.2
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
  rw [RootDatum.sl2_U, range_transvectionHom_reflectionPerm] at hg
  exact (mem_range_transvectionHom_iff _).mp hg

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

/-- The standard valuation of `SL₂(K)` is discrete exactly when the value set `ω (Kˣ)` meets
every closed bounded interval of `ℝ` in a finite set. -/
private theorem isDiscrete_sl2_iff_finite :
    (sl2 R ω hω).IsDiscrete ↔
      ∀ r s : ℝ, ({t : ℝ | ∃ x : K, x ≠ 0 ∧ ω x = t} ∩ Set.Icc r s).Finite := by
  simp only [isDiscrete_iff, valueSet_sl2]
  exact ⟨fun h ↦ h ⟨0, by norm_num⟩, fun h _ ↦ h⟩

/-- The standard valuation of `SL₂(K)` is discrete exactly when the positive values of `ω` are
bounded away from `0`, that is, when `ω` is a discrete valuation of `K`. -/
theorem isDiscrete_sl2_iff :
    (sl2 R ω hω).IsDiscrete ↔ ∃ ε : ℝ, 0 < ε ∧ ∀ x : K, 0 < ω x → (ε : WithTop ℝ) ≤ ω x := by
  rw [isDiscrete_sl2_iff_finite]
  constructor
  · -- `ε` is a lower bound of the positive values of `ω`, with `ε > 0`.
    intro h
    obtain ⟨ε, hε, hmin⟩ := exists_lt_forall_le_of_finite_inter_Ioo one_pos
      ((h 0 1).subset (Set.inter_subset_inter_right _ Set.Ioo_subset_Icc_self))
    refine ⟨ε, hε, fun x hx ↦ ?_⟩
    rcases eq_or_ne (ω x) ⊤ with h0 | h0
    · simp [h0]
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp h0
    rw [← ht] at hx ⊢
    have hx0 : x ≠ 0 := fun h ↦ by simp [h] at ht
    exact_mod_cast hmin t ⟨x, hx0, ht.symm⟩ (by exact_mod_cast hx)
  · -- Two values `a < b` of `ω` differ by the value `b - a = ω (y * x⁻¹)`, so by at least `ε`.
    rintro ⟨ε, hε, hsep⟩
    refine finite_inter_Icc_of_forall_le_sub hε ?_
    rintro a ⟨x, -, hx⟩ b ⟨y, -, hy⟩ hab
    have hyx : ω (y * x⁻¹) = ((b - a : ℝ) : WithTop ℝ) := by
      simp [hx, hy, sub_eq_add_neg]
    have hle := hsep (y * x⁻¹) (by rw [hyx]; exact_mod_cast sub_pos.mpr hab)
    rwa [hyx, WithTop.coe_le_coe] at hle

/-- If `ω` takes only integer values on `Kˣ`, as a normalized discrete valuation does, then the
standard valuation of `SL₂(K)` is discrete. -/
theorem isDiscrete_sl2_of_forall_exists_int
    (h : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ω x = ((n : ℝ) : WithTop ℝ)) : (sl2 R ω hω).IsDiscrete := by
  refine (isDiscrete_sl2_iff R ω hω).mpr ⟨1, one_pos, fun x hx ↦ ?_⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  obtain ⟨n, hn⟩ := h x hx0
  rw [hn] at hx ⊢
  have hn0 : 0 < n := by exact_mod_cast hx
  exact_mod_cast (by omega : (1 : ℤ) ≤ n)

/-- If every rational number is a value of `ω`, then the standard valuation of `SL₂(K)` is not
discrete: `ω` takes arbitrarily small positive values. -/
theorem not_isDiscrete_sl2_of_forall_rat (h : ∀ q : ℚ, ∃ x : K, ω x = ((q : ℝ) : WithTop ℝ)) :
    ¬(sl2 R ω hω).IsDiscrete := by
  rw [isDiscrete_sl2_iff]
  rintro ⟨ε, hε, hsep⟩
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  obtain ⟨x, hx⟩ := h q
  have := hsep x (by rw [hx]; exact_mod_cast hq0)
  rw [hx, WithTop.coe_le_coe] at this
  exact hqε.not_ge this

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

/-- Read in `WithTop ℝ`, the valuation map of the diagonal torus sends `diag(t, t⁻¹)` to
`-ω t`. -/
theorem coe_sl2TorusValuationMap_apply (ω : AddValuation K (WithTop ℝ))
    (z : (RootDatum.sl2 ℝ K).T) (j : Fin 1) :
    (sl2TorusValuationMap ω z j : WithTop ℝ) =
      -ω (((z : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) := by
  rw [sl2TorusValuationMap_apply, WithTop.LinearOrderedAddCommGroup.coe_neg,
    WithTop.coe_untop₀_of_ne_top
      ((ω.ne_top_iff).mpr (apply_self_ne_zero_of_mem_diagonalTorus z.property 0))]

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
    WithTop.untop₀_add ((ω.ne_top_iff).mpr (apply_self_ne_zero_of_mem_diagonalTorus z.property 0))
      ((ω.ne_top_iff).mpr (apply_self_ne_zero_of_mem_diagonalTorus w.property 0)), neg_add]

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
    SL2.apply_conj_diagonal ω _ hz, transvection_apply_same]

end Valuation

end TauCeti.BruhatTits
