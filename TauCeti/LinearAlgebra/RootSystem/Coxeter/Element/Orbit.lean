/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import TauCeti.GroupTheory.Coxeter.CoxeterElement
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Conj
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Plane
import TauCeti.LinearAlgebra.RootSystem.Coxeter.FixedPoints
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Irreducible
import TauCeti.LinearAlgebra.RootSystem.LongestElement

/-!
# Steinberg's Coxeter orbits on roots and the root-count formula `|Φ| = r · h`

For a finite, reduced, crystallographic root pairing `P` with base `b` of rank `r = b.support.card`
and any Coxeter element `c = wordProd P b l` of order `h = orderOf c`, this file proves Steinberg's
root-orbit theorem and Bourbaki's uniform root-count formula without assuming root spanning:
1. **Inversions** (`TauCeti.ncard_inversions_wordProd_eq_card_support`): `c` has `r` inversions.
2. **Free cyclic orbits** (`RootPairing.Base.weylGroupToPerm_wordProd_pow_apply_eq_self_iff`,
   `RootPairing.Base.minimalPeriod_weylGroupToPerm_wordProd`): every `⟨c⟩`-orbit on `ι` has minimal
   period and cardinality `h`.
3. **Unique inversion per orbit and `|Φ| = r · h`**
   (`RootPairing.Base.natCard_eq_card_support_mul_orderOf_wordProd`,
   `RootPairing.Base.existsUnique_sameCycle_mem_inversions_wordProd`,
   `RootPairing.Base.existsUnique_pow_mem_inversions_wordProd`): invariance under
   `TauCeti.longestElement` forces a sign change on every orbit, and sinusoidal variation on
   Coleman's Coxeter plane makes this crossing unique, giving `r` orbits of size `h`.
4. **Exceptional root counts** (`RootPairing.natCard_eq_of_hasCartanType_E8`,
   `RootPairing.ncard_posRoots_of_hasCartanType_E8`, and `E₆`, `E₇`, `F₄`, `G₂`): `240` (`120`),
   `126` (`63`), `72` (`36`), `48` (`24`), and `12` (`6`) roots (positive roots).

## References
* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. **91** (1959), 493–504.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2; Ch. VI, §1, no. 11.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, §§ 3.16–3.18.
-/

public section

open Matrix RootPairing TauCeti

/-! ### Inversions of duplicate-free words and Coxeter elements -/

namespace TauCeti

section Inversions

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-- A word in the simple reflections without repeated letters has as many inversions as letters. -/
theorem ncard_inversions_wordProd_of_nodup {l : List b.support} (hl : l.Nodup) :
    (inversions P b (wordProd P b l)).ncard = l.length :=
  (isReduced_weylCoxeterSystem_iff P b l).mp ((weylCoxeterSystem P b).isReduced_of_nodup hl)

/-- **Every Coxeter element has `b.support.card` inversions.** -/
theorem ncard_inversions_wordProd_eq_card_support {l : List b.support} (hl : l.Nodup)
    (hall : ∀ i, i ∈ l) :
    (inversions P b (wordProd P b l)).ncard = b.support.card := by
  rw [← length_weylCoxeterSystem_eq, ← weylCoxeterSystem_wordProd,
    (weylCoxeterSystem P b).length_wordProd_eq_card hl hall, Fintype.card_coe]

/-- The bipartite Coxeter element of any two-colouring of the Coxeter graph has `b.support.card`
inversions. -/
theorem ncard_inversions_bipartiteCoxeterElement
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    (inversions P b ((weylCoxeterSystem P b).bipartiteCoxeterElement col)).ncard =
      b.support.card := by
  rw [← length_weylCoxeterSystem_eq, (weylCoxeterSystem P b).length_bipartiteCoxeterElement col,
    Fintype.card_coe]

end Inversions

end TauCeti

/-! ### Free Coxeter orbits on roots and `|Φ| = r · h` -/

namespace RootPairing.Base

section TrigonometricSignChange

private lemma exists_shift_mem_of_cos_pos_of_cos_add_nonpos {δ α : ℝ}
    (hδ0 : 0 < δ) (hδpi : δ ≤ Real.pi) (hcos : 0 < Real.cos α) (hcos_add : Real.cos (α + δ) ≤ 0) :
    ∃ m : ℤ, Real.pi / 2 - δ ≤ α - m * (2 * Real.pi) ∧ α - m * (2 * Real.pi) < Real.pi / 2 := by
  have h2pi : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
  let m : ℤ := ⌊(α + Real.pi) / (2 * Real.pi)⌋
  set β : ℝ := α - m * (2 * Real.pi)
  have hlo : -Real.pi ≤ β := by
    linarith [(le_div_iff₀ h2pi).mp (Int.floor_le ((α + Real.pi) / (2 * Real.pi)))]
  have hhi : β < Real.pi := by
    linarith [(div_lt_iff₀ h2pi).mp (Int.lt_floor_add_one ((α + Real.pi) / (2 * Real.pi)))]
  have hcosβ : 0 < Real.cos β := by rwa [Real.cos_sub_int_mul_two_pi]
  have hβ_gt : -(Real.pi / 2) < β := by
    by_contra! hle
    have hnp := Real.cos_nonpos_of_pi_div_two_le_of_le (x := -β) (by linarith) (by linarith)
    rw [Real.cos_neg] at hnp; linarith
  have hβ_lt : β < Real.pi / 2 := by
    by_contra! hge
    linarith [Real.cos_nonpos_of_pi_div_two_le_of_le (x := β) hge (by linarith [Real.pi_pos])]
  have hβ_ge : Real.pi / 2 - δ ≤ β := by
    by_contra! hlt
    have hpos := Real.cos_pos_of_mem_Ioo (x := β + δ) ⟨by linarith, by linarith⟩
    have hca : Real.cos (β + δ) = Real.cos (α + δ) := by
      rw [show β + δ = α + δ - m * (2 * Real.pi) by ring, Real.cos_sub_int_mul_two_pi]
    linarith
  exact ⟨m, hβ_ge, hβ_lt⟩

private lemma eq_of_cos_sign_change_fin {h : ℕ} (hh : 2 ≤ h) (α₀ : ℝ) {k₁ k₂ : Fin h}
    (hpos₁ : 0 < Real.cos (α₀ + 2 * Real.pi * (k₁ : ℝ) / h))
    (hneg₁ : Real.cos (α₀ + 2 * Real.pi * ((k₁ : ℝ) + 1) / h) ≤ 0)
    (hpos₂ : 0 < Real.cos (α₀ + 2 * Real.pi * (k₂ : ℝ) / h))
    (hneg₂ : Real.cos (α₀ + 2 * Real.pi * ((k₂ : ℝ) + 1) / h) ≤ 0) :
    k₁ = k₂ := by
  have hh_pos : (0 : ℝ) < h := by positivity
  set δ : ℝ := 2 * Real.pi / h
  have hδ0 : 0 < δ := div_pos (by linarith [Real.pi_pos]) hh_pos
  have hδpi : δ ≤ Real.pi := (div_le_iff₀ hh_pos).mpr (by
    have : (2 : ℝ) ≤ h := by exact_mod_cast hh
    nlinarith [Real.pi_pos])
  have h2pi : 2 * Real.pi = (h : ℝ) * δ := by simp [δ, mul_div_cancel₀ _ hh_pos.ne']
  have hk (k : ℝ) : 2 * Real.pi * k / h = k * δ := by simp only [δ]; ring
  obtain ⟨m₁, hlo₁, hhi₁⟩ := exists_shift_mem_of_cos_pos_of_cos_add_nonpos hδ0 hδpi hpos₁
    (by rwa [show α₀ + 2 * Real.pi * (k₁ : ℝ) / h + δ =
      α₀ + 2 * Real.pi * ((k₁ : ℝ) + 1) / h by simp only [δ]; ring])
  obtain ⟨m₂, hlo₂, hhi₂⟩ := exists_shift_mem_of_cos_pos_of_cos_add_nonpos hδ0 hδpi hpos₂
    (by rwa [show α₀ + 2 * Real.pi * (k₂ : ℝ) / h + δ =
      α₀ + 2 * Real.pi * ((k₂ : ℝ) + 1) / h by simp only [δ]; ring])
  set n : ℤ := (k₂ : ℤ) - (k₁ : ℤ) - (m₂ - m₁) * (h : ℤ)
  have hdiff : (n : ℝ) * δ = (α₀ + 2 * Real.pi * (k₂ : ℝ) / h - m₂ * (2 * Real.pi)) -
      (α₀ + 2 * Real.pi * (k₁ : ℝ) / h - m₁ * (2 * Real.pi)) := by
    push_cast [n]; rw [hk, hk, h2pi]; ring
  have hn_gt : (-1 : ℤ) < n := by
    have : ((-1 : ℤ) : ℝ) * δ < (n : ℝ) * δ := by push_cast; linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hδ0.le
  have hn_lt : n < (1 : ℤ) := by
    have : (n : ℝ) * δ < ((1 : ℤ) : ℝ) * δ := by push_cast; linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hδ0.le
  have hdvd : (h : ℤ) ∣ ((k₂ : ℤ) - (k₁ : ℤ)) := ⟨m₂ - m₁, by rw [mul_comm]; omega⟩
  have hnat_zero : ((k₂ : ℤ) - (k₁ : ℤ)).natAbs = 0 :=
    Nat.eq_zero_of_dvd_of_lt (by simpa using Int.natAbs_dvd_natAbs.mpr hdvd) (by omega)
  exact Fin.ext (by omega)

end TrigonometricSignChange

section Orbits

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- **Steinberg's freeness of Coxeter orbits on roots** (Cartan-matrix form): when `b.cartanMatrix`
is of finite type with preconnected Dynkin diagram, `c ^ k` fixes `j` if and only if
`orderOf c ∣ k`. -/
theorem weylGroupToPerm_wordProd_pow_apply_eq_self_iff_of_isFiniteType (b : P.Base)
    (hft : IsFiniteType b.cartanMatrix) (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) (j : ι) (k : ℕ) :
    P.weylGroupToPerm (wordProd P b l ^ k) j = j ↔ orderOf (wordProd P b l) ∣ k := by
  classical
  set c := wordProd P b l
  refine ⟨fun hfix ↦ ?_, fun hdvd ↦ ?_⟩
  · have : Nonempty ι := ⟨j⟩
    have hW := b.actsBy_wordProd l
    obtain ⟨z, -, hz_eig, hz_prim, hz_reg, -⟩ :=
      b.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd_of_isFiniteType hft hconn hnd hall hW
    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (orderOf c : ℂ))
    set W_ℂ := (l.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℂ)
    have hWpow (m : ℕ) : (W_ℂ ^ m) *ᵥ z = (ζ ^ m) • z := by
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hz_eig, smul_smul, ← pow_succ]
    have hfix_inv : P.weylGroupToPerm (c ^ k)⁻¹ j = j :=
      (P.weylGroupToPerm (c ^ k)).injective (by
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply, hfix])
    have heval := b.corootEval_weylGroupToPerm_inv (hW.pow k) ℂ j z
    rw [hfix_inv, Matrix.map_pow, hWpow k, map_smul, smul_eq_mul] at heval
    exact hz_prim.dvd_of_pow_eq_one k (mul_right_cancel₀ (hz_reg j) (by linear_combination -heval))
  · rw [orderOf_dvd_iff_pow_eq_one.mp hdvd, map_one, Equiv.Perm.one_apply]

/-- **Steinberg's freeness of Coxeter orbits on roots.** For any Coxeter element
`c = wordProd P b l` of an irreducible finite crystallographic reduced root pairing and any root
index `j : ι`, the power `c ^ k` fixes `j` if and only if `orderOf c ∣ k`. -/
theorem weylGroupToPerm_wordProd_pow_apply_eq_self_iff [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) (j : ι) (k : ℕ) :
    P.weylGroupToPerm (wordProd P b l ^ k) j = j ↔ orderOf (wordProd P b l) ∣ k := by
  have : Nonempty ι := ⟨j⟩; have : NeZero (2 : R) := ⟨by norm_num⟩
  exact b.weylGroupToPerm_wordProd_pow_apply_eq_self_iff_of_isFiniteType
    (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall j k

/-- Every root index `j : ι` has minimal period `orderOf (wordProd P b l)` under `wordProd P b l`
when `b.cartanMatrix` is of finite type with preconnected Dynkin diagram. -/
theorem minimalPeriod_weylGroupToPerm_wordProd_of_isFiniteType (b : P.Base)
    (hft : IsFiniteType b.cartanMatrix) (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) (j : ι) :
    Function.minimalPeriod (P.weylGroupToPerm (wordProd P b l)) j = orderOf (wordProd P b l) := by
  have := P.finite_weylGroup_of_base b
  set c := wordProd P b l
  set σ := P.weylGroupToPerm c
  have hper : Function.IsPeriodicPt σ (orderOf c) j := by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow, ← map_pow,
      pow_orderOf_eq_one, map_one, Equiv.Perm.one_apply]
  refine Nat.dvd_antisymm hper.minimalPeriod_dvd ?_
  rw [← b.weylGroupToPerm_wordProd_pow_apply_eq_self_iff_of_isFiniteType hft hconn hnd hall j]
  have hm := Function.isPeriodicPt_minimalPeriod σ j
  rwa [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow, ← map_pow] at hm

/-- Every root index `j : ι` has minimal period `orderOf (wordProd P b l)` under a Coxeter element
`wordProd P b l`. -/
theorem minimalPeriod_weylGroupToPerm_wordProd [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) (j : ι) :
    Function.minimalPeriod (P.weylGroupToPerm (wordProd P b l)) j = orderOf (wordProd P b l) := by
  have : Nonempty ι := ⟨j⟩; have : NeZero (2 : R) := ⟨by norm_num⟩
  exact b.minimalPeriod_weylGroupToPerm_wordProd_of_isFiniteType
    (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall j

/-- Every `⟨wordProd P b l⟩`-orbit on the root indices has cardinality `orderOf (wordProd P b l)`
when `b.cartanMatrix` is of finite type with preconnected Dynkin diagram. -/
theorem ncard_sameCycle_weylGroupToPerm_wordProd_of_isFiniteType (b : P.Base)
    (hft : IsFiniteType b.cartanMatrix) (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) (j : ι) :
    {k : ι | Equiv.Perm.SameCycle (P.weylGroupToPerm (wordProd P b l)) j k}.ncard =
      orderOf (wordProd P b l) := by
  rw [Equiv.Perm.ncard_setOf_sameCycle (P.weylGroupToPerm (wordProd P b l)) j,
    b.minimalPeriod_weylGroupToPerm_wordProd_of_isFiniteType hft hconn hnd hall j]

/-- Every `⟨wordProd P b l⟩`-orbit on the root indices has cardinality `orderOf (wordProd P b l)`.
-/
theorem ncard_sameCycle_weylGroupToPerm_wordProd [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) (j : ι) :
    {k : ι | Equiv.Perm.SameCycle (P.weylGroupToPerm (wordProd P b l)) j k}.ncard =
      orderOf (wordProd P b l) := by
  rw [Equiv.Perm.ncard_setOf_sameCycle, b.minimalPeriod_weylGroupToPerm_wordProd hnd hall j]

/-- A nonempty subset of roots whose sum is fixed by `longestElement P b` contains both a positive
root and a negative root (requiring no spanning hypothesis on `P`). -/
private theorem exists_isPos_and_not_isPos_of_longestElement_smul_sum_eq_self (b : P.Base)
    {O : Finset ι} (hOne : O.Nonempty)
    (hw₀ : longestElement P b • ∑ y ∈ O, P.root y = ∑ y ∈ O, P.root y) :
    (∃ y ∈ O, b.IsPos y) ∧ (∃ y ∈ O, ¬ b.IsPos y) := by
  set w₀ := longestElement P b
  have hnot_all_pos {S : Finset ι} (hSne : S.Nonempty)
      (hS : w₀ • ∑ y ∈ S, P.root y = ∑ y ∈ S, P.root y) : ∃ y ∈ S, ¬ b.IsPos y := by
    by_contra! hall_pos
    set s : M := ∑ y ∈ S, P.root y
    have hneg_root (z : ι) : -P.root z = P.root (P.reflectionPerm z z) := by
      rw [P.root_reflectionPerm, P.reflection_apply_self]
    have hs_cone : s ∈ posRootCone P b := AddSubmonoid.sum_mem _ fun y hy ↦
      root_mem_posRootCone_of_mem_posRoots P b ((mem_posRoots P b y).mpr (hall_pos y hy))
    have hns_cone : -s ∈ posRootCone P b := by
      rw [← hS, show -(w₀ • s) = ∑ y ∈ S, P.root
          (P.reflectionPerm (P.weylGroupToPerm w₀ y) (P.weylGroupToPerm w₀ y)) by
        simp only [s, Finset.smul_sum, P.weylGroup_apply_root, ← Finset.sum_neg_distrib, hneg_root]]
      exact AddSubmonoid.sum_mem _ fun y hy ↦ root_mem_posRootCone_of_mem_posRoots P b
        ((reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b _).mpr
          (mapsTo_posRoots_negRoots_longestElement P b ((mem_posRoots P b y).mpr (hall_pos y hy))))
    exact sum_root_ne_zero_of_mem_posRoots P b hSne (f := id)
      (fun y hy ↦ (mem_posRoots P b y).mpr (hall_pos y hy))
      ((isPointed_posRootCone P b).eq_zero_of_mem_of_neg_mem hs_cone hns_cone)
  refine ⟨?_, hnot_all_pos hOne hw₀⟩
  have himg_sum : ∑ z ∈ O.map (P.weylGroupToPerm w₀).toEmbedding, P.root z = ∑ y ∈ O, P.root y := by
    rw [Finset.sum_map]
    simpa only [Equiv.coe_toEmbedding, Finset.smul_sum, P.weylGroup_apply_root] using hw₀
  obtain ⟨_, hz, hnot_pos⟩ := hnot_all_pos hOne.map (by rwa [himg_sum])
  obtain ⟨y, hyO, rfl⟩ := Finset.mem_map.mp hz
  dsimp only [Equiv.coe_toEmbedding] at hnot_pos
  refine ⟨y, hyO, ?_⟩
  by_contra hy_neg
  exact hnot_pos ((mem_posRoots P b _).mp
    (mapsTo_negRoots_posRoots_longestElement P b ((mem_negRoots P b y).mpr hy_neg)))

private theorem exists_sameCycle_mem_inversions_wordProd (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) (j : ι) :
    ∃ k : ι, Equiv.Perm.SameCycle (P.weylGroupToPerm (wordProd P b l)) j k ∧
      k ∈ inversions P b (wordProd P b l) := by
  let := Fintype.ofFinite ι
  classical
  set c := wordProd P b l
  set σ := P.weylGroupToPerm c
  let O : Finset ι := Finset.univ.filter fun y ↦ Equiv.Perm.SameCycle σ y j
  have hOne : O.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Equiv.Perm.SameCycle.rfl⟩⟩
  have hcs : c • ∑ y ∈ O, P.root y = ∑ y ∈ O, P.root y := by
    rw [Finset.smul_sum]; simp_rw [P.weylGroup_apply_root]
    exact Equiv.Perm.sum_filter_sameCycle_comp σ j P.root
  have hw₀ : longestElement P b • ∑ y ∈ O, P.root y = ∑ y ∈ O, P.root y :=
    (wordProd_smul_eq_self_iff_forall_smul_eq_self b hnd hall).mp hcs (longestElement P b)
  obtain ⟨⟨y₁, hy₁O, hy₁_pos⟩, ⟨y₂, hy₂O, hy₂_neg⟩⟩ :=
    exists_isPos_and_not_isPos_of_longestElement_smul_sum_eq_self b hOne hw₀
  have hsc₁ : Equiv.Perm.SameCycle σ j y₁ := ((Finset.mem_filter.mp hy₁O).2).symm
  have hsc₁₂ : Equiv.Perm.SameCycle σ y₁ y₂ :=
    ((Finset.mem_filter.mp hy₁O).2).trans ((Finset.mem_filter.mp hy₂O).2).symm
  obtain ⟨n, hn⟩ := hsc₁₂.exists_nat_pow_eq
  clear hsc₁₂ hy₂O
  induction n generalizing y₂ with
  | zero => exact (hy₂_neg (hn ▸ hy₁_pos)).elim
  | succ n ih =>
    by_cases hmid : b.IsPos ((σ ^ n) y₁)
    · refine ⟨(σ ^ n) y₁, hsc₁.trans ⟨n, by simp⟩, (mem_inversions P b c _).mpr ⟨hmid, ?_⟩⟩
      rwa [← Equiv.Perm.mul_apply, ← pow_succ', hn]
    · exact ih ((σ ^ n) y₁) hmid rfl

private theorem natCard_eq_card_quotient_mul_orderOf_wordProd (b : P.Base)
    (hft : IsFiniteType b.cartanMatrix) (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι =
      Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (P.weylGroupToPerm (wordProd P b l)))) *
        orderOf (wordProd P b l) := by
  let := Fintype.ofFinite ι
  classical
  set c := wordProd P b l
  set σ := P.weylGroupToPerm c
  let π : ι → Quotient (Equiv.Perm.SameCycle.setoid σ) :=
    Quotient.mk (Equiv.Perm.SameCycle.setoid σ)
  have hfib (q : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
      (Finset.univ.filter fun y ↦ π y = q).card = orderOf c := by
    have hset : (Finset.univ.filter fun y ↦ π y = q) =
        (Finset.univ.filter fun y ↦ Equiv.Perm.SameCycle σ q.out y) := by
      ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, π]
      exact ⟨fun hy ↦ (Quotient.exact (hy.trans q.out_eq.symm)).symm,
        fun hy ↦ (Quotient.sound hy.symm).trans q.out_eq⟩
    rw [hset, ← b.ncard_sameCycle_weylGroupToPerm_wordProd_of_isFiniteType hft hconn hnd hall q.out,
      ← Set.ncard_coe_finset]
    congr 1; ext y; exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ y))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := π) (t := Finset.univ) (fun x _ ↦ Finset.mem_univ _)]
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]

private theorem subsingleton_fin_pow_mem_inversions_bipartite_of_isFiniteType (b : P.Base)
    [Nontrivial b.support] (hft : IsFiniteType b.cartanMatrix)
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) (j : ι)
    {m₁ m₂ : Fin (orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement col))}
    (hm₁ : P.weylGroupToPerm ((weylCoxeterSystem P b).bipartiteCoxeterElement col ^ (m₁ : ℕ)) j ∈
      inversions P b ((weylCoxeterSystem P b).bipartiteCoxeterElement col))
    (hm₂ : P.weylGroupToPerm ((weylCoxeterSystem P b).bipartiteCoxeterElement col ^ (m₂ : ℕ)) j ∈
      inversions P b ((weylCoxeterSystem P b).bipartiteCoxeterElement col)) :
    m₁ = m₂ := by
  classical
  have := P.finite_weylGroup_of_base b
  let c₀ := (weylCoxeterSystem P b).bipartiteCoxeterElement col
  let h := orderOf c₀
  obtain ⟨e₁, e₂, -, -, -, hWinv_pow, hsector⟩ :=
    b.exists_coxeterPlane_bipartiteCoxeterElement_of_isFiniteType hft hconn col
  have hh_ge_two : 2 ≤ h := by
    have := orderOf_pos c₀
    have hne1 : h ≠ 1 := fun h1 ↦
      (weylCoxeterSystem P b).bipartiteCoxeterElement_ne_one col (orderOf_eq_one_iff.mp h1)
    omega
  have hh_pos : (0 : ℝ) < h := by positivity
  set φ₀ : ℝ := Real.pi / (2 * h)
  have hφ₀_lt : φ₀ < Real.pi / h := by
    rw [div_lt_div_iff₀ (by positivity) hh_pos]; nlinarith [Real.pi_pos]
  have hy₀ : ∀ k : b.support, 0 < b.corootEval ℝ (k : ι) (Real.cos φ₀ • e₁ + Real.sin φ₀ • e₂) :=
    hsector φ₀ (div_pos Real.pi_pos (by positivity)) hφ₀_lt
  set z : ℂ := ⟨b.corootEval ℝ j e₁, b.corootEval ℝ j e₂⟩
  have hcos_formula (φ : ℝ) :
      b.corootEval ℝ j (Real.cos φ • e₁ + Real.sin φ • e₂) = ‖z‖ * Real.cos (φ - z.arg) := by
    have hre : b.corootEval ℝ j e₁ = ‖z‖ * Real.cos z.arg := (Complex.norm_mul_cos_arg z).symm
    have him : b.corootEval ℝ j e₂ = ‖z‖ * Real.sin z.arg := (Complex.norm_mul_sin_arg z).symm
    simp only [map_add, map_smul, smul_eq_mul, hre, him, Real.cos_sub]; ring
  have hnorm_pos : 0 < ‖z‖ := (norm_nonneg z).lt_of_ne' fun h0 ↦
    b.corootEval_ne_zero_of_forall_pos hy₀ j (by rw [hcos_formula φ₀, h0, zero_mul])
  have hisPos_iff (k : ℕ) : b.IsPos (P.weylGroupToPerm (c₀ ^ k) j) ↔
      0 < Real.cos (φ₀ - z.arg + 2 * Real.pi * k / h) := by
    rw [← mem_posRoots, ← b.corootEval_pos_iff_mem_posRoots hy₀]
    have heq := b.corootEval_weylGroupToPerm_inv
      ((b.actsBy_bipartiteCoxeterElement_inv col).pow k) ℝ j (Real.cos φ₀ • e₁ + Real.sin φ₀ • e₂)
    rw [inv_pow, inv_inv, Matrix.map_pow, hWinv_pow k φ₀, hcos_formula] at heq
    rw [heq, show φ₀ + 2 * Real.pi * k / h - z.arg = φ₀ - z.arg + 2 * Real.pi * k / h by ring]
    exact mul_pos_iff_of_pos_left hnorm_pos
  have hstep (m : Fin h) (hm : P.weylGroupToPerm (c₀ ^ (m : ℕ)) j ∈ inversions P b c₀) :
      0 < Real.cos (φ₀ - z.arg + 2 * Real.pi * (m : ℝ) / h) ∧
        Real.cos (φ₀ - z.arg + 2 * Real.pi * ((m : ℝ) + 1) / h) ≤ 0 := by
    obtain ⟨hp, hn⟩ := (mem_inversions P b c₀ _).mp hm
    rw [← Equiv.Perm.mul_apply, ← map_mul, ← pow_succ'] at hn
    rw [hisPos_iff] at hp hn
    exact ⟨hp, not_lt.mp (by push_cast at hn; exact hn)⟩
  exact eq_of_cos_sign_change_fin hh_ge_two (φ₀ - z.arg)
    (hstep m₁ hm₁).1 (hstep m₁ hm₁).2 (hstep m₂ hm₂).1 (hstep m₂ hm₂).2

private theorem natCard_eq_card_support_mul_orderOf_wordProd_subsingleton (b : P.Base)
    [Subsingleton b.support] (hft : IsFiniteType b.cartanMatrix)
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) := by
  let := Fintype.ofFinite ι
  by_cases hne : Nonempty b.support
  · obtain ⟨i₀⟩ := hne
    have hcard_supp : b.support.card = 1 := by
      rw [← Fintype.card_coe]
      exact Fintype.card_eq_one_iff.mpr ⟨i₀, fun j ↦ Subsingleton.elim j i₀⟩
    have hl_eq : l = [i₀] := by
      obtain ⟨a, tail, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem (hall i₀))
      rw [List.nodup_cons] at hnd
      rw [List.eq_nil_iff_forall_not_mem.mpr fun x hx ↦ hnd.1 (Subsingleton.elim x a ▸ hx),
        Subsingleton.elim a i₀]
    set c := wordProd P b l
    have hword_pow (lw : List b.support) : wordProd P b lw = c ^ lw.length := by
      induction lw with
      | nil => simp
      | cons a lw ih =>
        have hc_eq : c = weylGroup.ofIdx P (a : ι) := by
          rw [show c = wordProd P b l from rfl, hl_eq, wordProd_cons, wordProd_nil, mul_one,
            Subsingleton.elim i₀ a]
        rw [wordProd_cons, ih, ← hc_eq, List.length_cons, pow_succ']
    have huniv : {k : ι | Equiv.Perm.SameCycle (P.weylGroupToPerm c) (i₀ : ι) k} = Set.univ := by
      refine Set.eq_univ_of_forall fun j ↦ ?_
      obtain ⟨i, hi, w, rfl⟩ := exists_mem_support_weylGroupToPerm_eq b j
      have hi_eq : i = (i₀ : ι) := congrArg Subtype.val (Subsingleton.elim (⟨i, hi⟩ : b.support) i₀)
      obtain ⟨lw, -, hw⟩ := (weylCoxeterSystem P b).exists_isReduced w
      rw [weylCoxeterSystem_wordProd, hword_pow] at hw
      exact ⟨lw.length, by rw [zpow_natCast, ← map_pow, hw, hi_eq]⟩
    have hncard :=
      b.ncard_sameCycle_weylGroupToPerm_wordProd_of_isFiniteType hft hconn hnd hall (i₀ : ι)
    rw [huniv, Set.ncard_univ] at hncard
    rw [hcard_supp, one_mul, hncard]
  · rw [not_nonempty_iff] at hne
    have : IsEmpty ι := ⟨fun j ↦ by
      obtain ⟨i, hi, -, -⟩ := exists_mem_support_weylGroupToPerm_eq b j; exact hne.false ⟨i, hi⟩⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero, ← Fintype.card_coe, Fintype.card_eq_zero,
      zero_mul]

private theorem card_quotient_sameCycle_bipartite_of_isFiniteType (b : P.Base)
    [Nontrivial b.support] (hft : IsFiniteType b.cartanMatrix)
    (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid
      (P.weylGroupToPerm ((weylCoxeterSystem P b).bipartiteCoxeterElement col)))) =
      b.support.card := by
  let := Fintype.ofFinite ι
  classical
  have := P.finite_weylGroup_of_base b
  obtain ⟨l₁, l₂, -, -, hnd₀, hall₀, hword₀⟩ :=
    (weylCoxeterSystem P b).exists_wordProd_eq_bipartiteCoxeterElement col
  rw [weylCoxeterSystem_wordProd] at hword₀
  let c₀ := (weylCoxeterSystem P b).bipartiteCoxeterElement col
  let σ₀ := P.weylGroupToPerm c₀
  let π₀ : ι → Quotient (Equiv.Perm.SameCycle.setoid σ₀) :=
    Quotient.mk (Equiv.Perm.SameCycle.setoid σ₀)
  have hfib_inv (q : Quotient (Equiv.Perm.SameCycle.setoid σ₀)) :
      ((inversionsFinset P b c₀).filter fun y ↦ π₀ y = q).card = 1 := by
    rw [Finset.card_eq_one]
    obtain ⟨k, hsc, hinv⟩ := hword₀ ▸ b.exists_sameCycle_mem_inversions_wordProd hnd₀ hall₀ q.out
    refine ⟨k, Finset.eq_singleton_iff_unique_mem.mpr
      ⟨Finset.mem_filter.mpr ⟨(mem_inversionsFinset P b c₀ k).mpr hinv,
        (Quotient.eq.mpr hsc.symm).trans q.out_eq⟩, fun y hy ↦ ?_⟩⟩
    obtain ⟨hy_inv, hy_q⟩ := Finset.mem_filter.mp hy
    obtain ⟨n₁, rfl⟩ := ((Quotient.exact (hy_q.trans q.out_eq.symm)).symm).exists_nat_pow_eq
    obtain ⟨n₂, rfl⟩ := hsc.exists_nat_pow_eq
    have hmod (n : ℕ) : (σ₀ ^ n) q.out = P.weylGroupToPerm (c₀ ^ (n % orderOf c₀)) q.out := by
      rw [← map_pow, ← pow_mod_orderOf]
    have hm_eq := b.subsingleton_fin_pow_mem_inversions_bipartite_of_isFiniteType hft hconn col
      q.out (m₁ := ⟨n₁ % orderOf c₀, Nat.mod_lt n₁ (orderOf_pos c₀)⟩)
      (m₂ := ⟨n₂ % orderOf c₀, Nat.mod_lt n₂ (orderOf_pos c₀)⟩)
      (hmod n₁ ▸ (mem_inversionsFinset P b c₀ _).mp hy_inv) (hmod n₂ ▸ hinv)
    have hrem : n₁ % orderOf c₀ = n₂ % orderOf c₀ := congrArg Fin.val hm_eq
    rw [hmod n₁, hmod n₂, hrem]
  rw [Nat.card_eq_fintype_card]
  have hsum := Finset.card_eq_sum_card_fiberwise (f := π₀) (s := inversionsFinset P b c₀)
    (t := Finset.univ) (fun x _ ↦ Finset.mem_univ _)
  simp only [hfib_inv, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  rw [← hsum, card_inversionsFinset, ncard_inversions_bipartiteCoxeterElement]

/-- **Bourbaki's root-count formula `|Φ| = r · h`** (Cartan-matrix form): when `b.cartanMatrix` is
of finite type with preconnected Dynkin diagram, the number of roots equals `b.support.card` times
the order of any Coxeter element `wordProd P b l` (requiring neither spanning nor irreducibility
over `R`). -/
theorem natCard_eq_card_support_mul_orderOf_wordProd_of_isFiniteType (b : P.Base)
    (hft : IsFiniteType b.cartanMatrix) (hconn : (diagramGraph b.cartanMatrix).Preconnected)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) := by
  classical
  by_cases hsub : Subsingleton b.support
  · exact b.natCard_eq_card_support_mul_orderOf_wordProd_subsingleton hft hconn hnd hall
  · have : Nontrivial b.support := not_subsingleton_iff_nontrivial.mp hsub
    have hacyc : (coxeterMatrixOfBase P b).graph.IsAcyclic := by
      rw [graph_coxeterMatrixOfBase]; exact hft.isAcyclic_diagramGraph
    obtain ⟨col⟩ : Nonempty ((coxeterMatrixOfBase P b).graph.Coloring Bool) :=
      Nonempty.map ((coxeterMatrixOfBase P b).graph.recolorOfEquiv finTwoEquiv) hacyc.isBipartite
    obtain ⟨l₁, l₂, -, -, hnd₀, hall₀, hword₀⟩ :=
      (weylCoxeterSystem P b).exists_wordProd_eq_bipartiteCoxeterElement col
    rw [weylCoxeterSystem_wordProd] at hword₀
    let c₀ := (weylCoxeterSystem P b).bipartiteCoxeterElement col
    let σ₀ := P.weylGroupToPerm c₀
    have hcard_Q₀ : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ₀)) = b.support.card :=
      b.card_quotient_sameCycle_bipartite_of_isFiniteType hft hconn col
    obtain ⟨u, hu⟩ : IsConj (wordProd P b l) c₀ := by
      rw [← weylCoxeterSystem_wordProd]
      exact (weylCoxeterSystem P b).isConj_wordProd_bipartiteCoxeterElement hacyc col hnd hall
    calc Nat.card ι
        = Nat.card (Quotient (Equiv.Perm.SameCycle.setoid
            (P.weylGroupToPerm (wordProd P b (l₁ ++ l₂))))) *
            orderOf (wordProd P b (l₁ ++ l₂)) :=
          b.natCard_eq_card_quotient_mul_orderOf_wordProd hft hconn hnd₀ hall₀
      _ = Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ₀)) * orderOf c₀ := by
          dsimp only [σ₀, c₀]; rw [hword₀]
      _ = b.support.card * orderOf (wordProd P b l) := by rw [hcard_Q₀, hu.orderOf_eq]

/-- **Bourbaki's root-count formula `|Φ| = r · h`.** In a finite, reduced, irreducible,
crystallographic root pairing with base `b`, the total number of roots equals the rank
`b.support.card` times the order of any Coxeter element `wordProd P b l`. -/
theorem natCard_eq_card_support_mul_orderOf_wordProd [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) := by
  let := Fintype.ofFinite ι
  by_cases hne : Nonempty ι
  · have : NeZero (2 : R) := ⟨by norm_num⟩
    exact b.natCard_eq_card_support_mul_orderOf_wordProd_of_isFiniteType
      (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall
  · have : IsEmpty ι := not_nonempty_iff.mp hne
    have : IsEmpty b.support := ⟨fun i ↦ IsEmpty.false i.1⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero, ← Fintype.card_coe, Fintype.card_eq_zero,
      zero_mul]

/-- **Positive-root count formula `2 |Φ⁺| = r · h`.** Twice the number of positive roots equals
`b.support.card * orderOf (wordProd P b l)`. -/
theorem two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    2 * (posRoots P b).ncard = b.support.card * orderOf (wordProd P b l) :=
  (two_mul_ncard_posRoots P b).trans (b.natCard_eq_card_support_mul_orderOf_wordProd hnd hall)

/-- **Positive-root count formula `|Φ⁺| = r · h / 2`.** -/
theorem ncard_posRoots_eq_card_support_mul_orderOf_wordProd_div_two [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    (posRoots P b).ncard = b.support.card * orderOf (wordProd P b l) / 2 := by
  rw [ncard_posRoots_eq_natCard_div_two, b.natCard_eq_card_support_mul_orderOf_wordProd hnd hall]

/-- **Number of Coxeter orbits on roots.** Every Coxeter element `wordProd P b l` partitions the
root indices `ι` into `b.support.card` cyclic orbits. -/
theorem card_quotient_sameCycle_weylGroupToPerm_wordProd [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (P.weylGroupToPerm (wordProd P b l)))) =
      b.support.card := by
  let := Fintype.ofFinite ι
  classical
  by_cases hne : Nonempty ι
  · have : NeZero (2 : R) := ⟨by norm_num⟩
    have := P.finite_weylGroup_of_base b
    have h1 := b.natCard_eq_card_quotient_mul_orderOf_wordProd
      (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall
    rw [b.natCard_eq_card_support_mul_orderOf_wordProd hnd hall] at h1
    exact Nat.mul_right_cancel (orderOf_pos (wordProd P b l)) h1.symm
  · have : IsEmpty ι := not_nonempty_iff.mp hne
    have : IsEmpty b.support := ⟨fun i ↦ IsEmpty.false i.1⟩
    have : IsEmpty (Quotient (Equiv.Perm.SameCycle.setoid
        (P.weylGroupToPerm (wordProd P b l)))) := ⟨Quotient.ind fun x ↦ IsEmpty.false x⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero, ← Fintype.card_coe, Fintype.card_eq_zero]

/-- **Steinberg's unique inversion per Coxeter orbit.** For any Coxeter element
`c = wordProd P b l` and any root `j : ι`, the `⟨c⟩`-orbit of `j` contains a unique root in
`inversions P b c`. -/
theorem existsUnique_sameCycle_mem_inversions_wordProd [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) (j : ι) :
    ∃! k : ι, Equiv.Perm.SameCycle (P.weylGroupToPerm (wordProd P b l)) j k ∧
      k ∈ inversions P b (wordProd P b l) := by
  let := Fintype.ofFinite ι
  classical
  set c := wordProd P b l
  set σ := P.weylGroupToPerm c
  let π : ι → Quotient (Equiv.Perm.SameCycle.setoid σ) :=
    Quotient.mk (Equiv.Perm.SameCycle.setoid σ)
  have hcard_Q : Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) = b.support.card := by
    rw [← Nat.card_eq_fintype_card]
    exact b.card_quotient_sameCycle_weylGroupToPerm_wordProd hnd hall
  have hle (q : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
      1 ≤ ((inversionsFinset P b c).filter fun y ↦ π y = q).card := by
    obtain ⟨k, hsc, hk⟩ := b.exists_sameCycle_mem_inversions_wordProd hnd hall q.out
    exact Finset.one_le_card.mpr ⟨k, Finset.mem_filter.mpr
      ⟨(mem_inversionsFinset P b c k).mpr hk, (Quotient.eq.mpr hsc.symm).trans q.out_eq⟩⟩
  have hsum : ∑ q : Quotient (Equiv.Perm.SameCycle.setoid σ),
      ((inversionsFinset P b c).filter fun y ↦ π y = q).card =
      ∑ _q : Quotient (Equiv.Perm.SameCycle.setoid σ), 1 := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := π) (s := inversionsFinset P b c)
      (t := Finset.univ) (fun x _ ↦ Finset.mem_univ _),
      card_inversionsFinset, ncard_inversions_wordProd_eq_card_support P b hnd hall,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hcard_Q]
  have hfib_j := (Finset.sum_eq_sum_iff_of_le fun q _ ↦ hle q).mp hsum.symm (π j)
    (Finset.mem_univ _)
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hfib_j.symm
  refine ⟨k, ?_, fun y ⟨hy_sc, hy_inv⟩ ↦ ?_⟩
  · obtain ⟨hk_inv, hk_q⟩ := Finset.mem_filter.mp (hk ▸ Finset.mem_singleton_self k)
    exact ⟨(Quotient.exact hk_q).symm, (mem_inversionsFinset P b c k).mp hk_inv⟩
  · have hmem : y ∈ (inversionsFinset P b c).filter fun z ↦ π z = π j :=
      Finset.mem_filter.mpr ⟨(mem_inversionsFinset P b c y).mpr hy_inv, Quotient.sound hy_sc.symm⟩
    exact Finset.mem_singleton.mp (hk ▸ hmem)

/-- Along the `Fin (orderOf c)`-parametrized `⟨c⟩`-orbit of `j`, a unique exponent `m` places
`c ^ m • α_j` in `inversions P b c`. -/
theorem existsUnique_pow_mem_inversions_wordProd [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) (j : ι) :
    ∃! m : Fin (orderOf (wordProd P b l)),
      P.weylGroupToPerm (wordProd P b l ^ (m : ℕ)) j ∈ inversions P b (wordProd P b l) := by
  have := P.finite_weylGroup_of_base b
  let c := wordProd P b l
  obtain ⟨k, ⟨hk_sc, hk_inv⟩, hk_uniq⟩ :=
    b.existsUnique_sameCycle_mem_inversions_wordProd hnd hall j
  obtain ⟨n, rfl⟩ := hk_sc.exists_nat_pow_eq
  let m₀ : Fin (orderOf c) := ⟨n % orderOf c, Nat.mod_lt n (orderOf_pos c)⟩
  have hm₀_eq : P.weylGroupToPerm (c ^ (m₀ : ℕ)) j = (P.weylGroupToPerm c ^ n) j := by
    dsimp only [m₀]; rw [pow_mod_orderOf, map_pow]
  refine ⟨m₀, by dsimp only; rwa [hm₀_eq], fun m hm ↦ ?_⟩
  have heq : P.weylGroupToPerm (c ^ (m : ℕ)) j = P.weylGroupToPerm (c ^ (m₀ : ℕ)) j :=
    (hk_uniq _ ⟨⟨(m : ℤ), by rw [zpow_natCast, map_pow]⟩, hm⟩).trans hm₀_eq.symm
  suffices ∀ a b' : Fin (orderOf c), (a : ℕ) ≤ (b' : ℕ) →
      P.weylGroupToPerm (c ^ (a : ℕ)) j = P.weylGroupToPerm (c ^ (b' : ℕ)) j → a = b' by
    rcases le_total m m₀ with hle | hle
    · exact this m m₀ hle heq
    · exact (this m₀ m hle heq.symm).symm
  intro a b' hle hab
  have hfix : P.weylGroupToPerm (c ^ ((b' : ℕ) - (a : ℕ))) j = j :=
    (P.weylGroupToPerm (c ^ (a : ℕ))).injective (by
      rw [← Equiv.Perm.mul_apply, ← map_mul, ← pow_add, Nat.add_sub_of_le hle, hab])
  have hdvd := (b.weylGroupToPerm_wordProd_pow_apply_eq_self_iff hnd hall j _).mp hfix
  have hlt : (b' : ℕ) < orderOf (wordProd P b l) := b'.isLt
  have h0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
  exact Fin.ext (by omega)

end Orbits

end RootPairing.Base

/-! ### Root counts for the exceptional Cartan types -/

namespace RootPairing

section ExceptionalRootCounts

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

private theorem natCard_eq_of_hasCartanType_aux {t : DynkinType} {h₀ n : ℕ}
    (ht : t.Valid) (hft : IsFiniteType t.cartanMatrix) (h : HasCartanType P b t)
    (hord : ∀ {l : List b.support}, l.Nodup → (∀ i, i ∈ l) → orderOf (wordProd P b l) = h₀)
    (hn : t.rank * h₀ = n) : Nat.card ι = n := by
  classical
  let l : List b.support := Finset.univ.toList
  have hnd : l.Nodup := Finset.nodup_toList _
  have hall : ∀ i, i ∈ l := fun i ↦ Finset.mem_toList.mpr (Finset.mem_univ i)
  obtain ⟨e, he⟩ := (hasCartanType_iff b t).mp h
  have hft_b : IsFiniteType b.cartanMatrix := (Matrix.ext he) ▸ hft.submatrix e.injective
  have hconn_b : (diagramGraph b.cartanMatrix).Preconnected := by
    let iso : diagramGraph b.cartanMatrix ≃g diagramGraph t.cartanMatrix :=
      ⟨e, fun {i j} ↦ by simp only [diagramGraph_adj, he, ne_eq, e.injective.eq_iff]⟩
    exact (iso.connected_iff.mpr (DynkinType.connected_diagramGraph_cartanMatrix ht)).preconnected
  rw [b.natCard_eq_card_support_mul_orderOf_wordProd_of_isFiniteType hft_b hconn_b hnd hall,
    h.card_support, hord hnd hall, hn]

/-- **A root pairing with a base of Cartan type `E₆` has `72` roots.** -/
theorem natCard_eq_of_hasCartanType_E6 (h : HasCartanType P b .E6) : Nat.card ι = 72 :=
  P.natCard_eq_of_hasCartanType_aux b DynkinType.valid_E6 DynkinType.isFiniteType_cartanMatrix_E6 h
    (fun hnd hall ↦ Coxeter.orderOf_wordProd_of_hasCartanType_E6 h hnd hall) rfl

/-- **A base of Cartan type `E₆` has `36` positive roots.** -/
theorem ncard_posRoots_of_hasCartanType_E6 (h : HasCartanType P b .E6) :
    (posRoots P b).ncard = 36 := by
  rw [ncard_posRoots_eq_natCard_div_two, P.natCard_eq_of_hasCartanType_E6 b h]

/-- **A root pairing with a base of Cartan type `E₇` has `126` roots.** -/
theorem natCard_eq_of_hasCartanType_E7 (h : HasCartanType P b .E7) : Nat.card ι = 126 :=
  P.natCard_eq_of_hasCartanType_aux b DynkinType.valid_E7 DynkinType.isFiniteType_cartanMatrix_E7 h
    (fun hnd hall ↦ Coxeter.orderOf_wordProd_of_hasCartanType_E7 h hnd hall) rfl

/-- **A base of Cartan type `E₇` has `63` positive roots.** -/
theorem ncard_posRoots_of_hasCartanType_E7 (h : HasCartanType P b .E7) :
    (posRoots P b).ncard = 63 := by
  rw [ncard_posRoots_eq_natCard_div_two, P.natCard_eq_of_hasCartanType_E7 b h]

/-- **A root pairing with a base of Cartan type `E₈` has `240` roots.** -/
theorem natCard_eq_of_hasCartanType_E8 (h : HasCartanType P b .E8) : Nat.card ι = 240 :=
  P.natCard_eq_of_hasCartanType_aux b DynkinType.valid_E8 DynkinType.isFiniteType_cartanMatrix_E8 h
    (fun hnd hall ↦ Coxeter.orderOf_wordProd_of_hasCartanType_E8 h hnd hall) rfl

/-- **A base of Cartan type `E₈` has `120` positive roots.** -/
theorem ncard_posRoots_of_hasCartanType_E8 (h : HasCartanType P b .E8) :
    (posRoots P b).ncard = 120 := by
  rw [ncard_posRoots_eq_natCard_div_two, P.natCard_eq_of_hasCartanType_E8 b h]

/-- **A root pairing with a base of Cartan type `F₄` has `48` roots.** -/
theorem natCard_eq_of_hasCartanType_F4 (h : HasCartanType P b .F4) : Nat.card ι = 48 :=
  P.natCard_eq_of_hasCartanType_aux b DynkinType.valid_F4 DynkinType.isFiniteType_cartanMatrix_F4 h
    (fun hnd hall ↦ Coxeter.orderOf_wordProd_of_hasCartanType_F4 h hnd hall) rfl

/-- **A base of Cartan type `F₄` has `24` positive roots.** -/
theorem ncard_posRoots_of_hasCartanType_F4 (h : HasCartanType P b .F4) :
    (posRoots P b).ncard = 24 := by
  rw [ncard_posRoots_eq_natCard_div_two, P.natCard_eq_of_hasCartanType_F4 b h]

/-- **A root pairing with a base of Cartan type `G₂` has `12` roots.** -/
theorem natCard_eq_of_hasCartanType_G2 (h : HasCartanType P b .G2) : Nat.card ι = 12 :=
  P.natCard_eq_of_hasCartanType_aux b DynkinType.valid_G2 DynkinType.isFiniteType_cartanMatrix_G2 h
    (fun hnd hall ↦ Coxeter.orderOf_wordProd_of_hasCartanType_G2 h hnd hall) rfl

/-- **A base of Cartan type `G₂` has `6` positive roots.** -/
theorem ncard_posRoots_of_hasCartanType_G2 (h : HasCartanType P b .G2) :
    (posRoots P b).ncard = 6 := by
  rw [ncard_posRoots_eq_natCard_div_two, P.natCard_eq_of_hasCartanType_G2 b h]

end ExceptionalRootCounts

end RootPairing

end
