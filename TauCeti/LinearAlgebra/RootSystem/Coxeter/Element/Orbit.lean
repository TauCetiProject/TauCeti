/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.FixedPoints
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.LinearAlgebra.RootSystem.Inversions.Length
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Angle
import TauCeti.Data.List.Pairwise
import TauCeti.GroupTheory.Coxeter.CoxeterElement
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.Cycle.Enumeration
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Plane
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Length
import TauCeti.LinearAlgebra.RootSystem.LongestElement
import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Basic

/-!
# Orbits of a Coxeter element on the roots and `|Φ| = r · h`

1. **General fixed-point-free orbit bounds (`TauCeti`)**: if `w` fixes no nonzero vector, every
   root reaches an inversion within `orderOf w` steps
   (`TauCeti.exists_lt_orderOf_weylGroupToPerm_pow_mem_inversions`), giving
   `|Φ| ≤ orderOf w * #inversions(w)` (`TauCeti.natCard_le_orderOf_mul_ncard_inversions`) and
   `|Φ| ≤ orderOf c * l.length` (`TauCeti.natCard_le_orderOf_wordProd_mul_length`).

2. **Steinberg's free Coxeter orbits and `|Φ| = r · h` (`RootPairing.Base`)**: for a finite,
   reduced, crystallographic root pairing `P` with base `b` of rank `r` whose Cartan matrix is of
   finite type with preconnected diagram (or `[P.IsIrreducible]`) and any Coxeter element
   `c = wordProd P b l` (with `l` duplicate-free and containing every simple root) of order `h`
   (without assuming root spanning):
   - **Free cyclic orbits** (`weylGroupToPerm_wordProd_pow_apply_eq_self_iff`,
     `minimalPeriod_weylGroupToPerm_wordProd`, `ncard_setOf_sameCycle_weylGroupToPerm_wordProd`).
   - **Unique inversion per orbit & `|Φ| = r · h`**
     (`card_quotient_sameCycle_weylGroupToPerm_wordProd`,
     `existsUnique_sameCycle_mem_inversions_wordProd`, `existsUnique_pow_mem_inversions_wordProd`,
     `ncard_posRoots_eq_card_support_mul_orderOf_wordProd_div_two`), plus `_of_isFiniteType` forms
     (including `natCard_eq_card_support_mul_orderOf_wordProd_of_isFiniteType`).

## References
* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. **91** (1959), 493–504.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2; Ch. VI, §1, no. 11.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, §§ 3.16–3.18.
-/

public section

namespace RootPairing.Base

section Orbits

open Matrix RootPairing TauCeti

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

private theorem exists_sameCycle_mem_inversions_wordProd (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) (j : ι) :
    ∃ k : ι, Equiv.Perm.SameCycle (P.weylGroupToPerm (wordProd P b l)) j k ∧
      k ∈ inversions P b (wordProd P b l) := by
  set c := wordProd P b l; set σ := P.weylGroupToPerm c
  obtain ⟨⟨y₁, hy₁O, hy₁_pos⟩, ⟨y₂, hy₂O, hy₂_neg⟩⟩ :=
    exists_isPos_and_not_isPos_of_longestElement_smul_sum_eq_self
      (P.orbitIndices_nonempty (c : P.Aut) j)
      ((wordProd_smul_eq_self_iff_forall_smul_eq_self b hnd hall).mp
        (P.orbitSum_def (c : P.Aut) j ▸ P.weightMap_orbitSum_self (c : P.Aut) j) _)
  have hσ : (c : P.Aut).indexEquiv = σ :=
    _root_.Equiv.ext fun i ↦ (P.weylGroupToPerm_apply c i).symm
  have hsc₁ : Equiv.Perm.SameCycle σ j y₁ := hσ ▸ P.mem_orbitIndices.mp hy₁O
  obtain ⟨n, hn⟩ := (hsc₁.symm.trans (hσ ▸ P.mem_orbitIndices.mp hy₂O)).exists_nat_pow_eq
  clear hy₂O; induction n generalizing y₂ with
  | zero => rw [pow_zero, Equiv.Perm.coe_one, id_eq] at hn; exact (hy₂_neg (hn ▸ hy₁_pos)).elim
  | succ n ih =>
    by_cases hmid : b.IsPos ((σ ^ n) y₁)
    · exact ⟨(σ ^ n) y₁, hsc₁.trans ⟨n, by simp⟩, (mem_inversions P b c _).mpr
        ⟨hmid, by rwa [← Equiv.Perm.mul_apply, ← pow_succ', hn]⟩⟩
    · exact ih ((σ ^ n) y₁) hmid rfl

private theorem surjective_quotientMk_inversions_wordProd (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    Function.Surjective fun k : inversions P b (wordProd P b l) ↦
      Quotient.mk (Equiv.Perm.SameCycle.setoid (P.weylGroupToPerm (wordProd P b l))) k.val :=
  Quotient.ind fun j ↦ let ⟨k, hsc, hinv⟩ := b.exists_sameCycle_mem_inversions_wordProd hnd hall j
    ⟨⟨k, hinv⟩, Quotient.sound hsc.symm⟩

omit [CharZero R] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] in
private theorem exists_fin_pow_eq_of_sameCycle {c : P.weylGroup} {j k : ι}
    (hc : 0 < orderOf c) (hsc : Equiv.Perm.SameCycle (P.weylGroupToPerm c) j k) :
    ∃ m : Fin (orderOf c), P.weylGroupToPerm (c ^ (m : ℕ)) j = k :=
  let ⟨i, hi, heq⟩ := hsc.exists_pow_eq'
  ⟨⟨i, hi.trans_le (Nat.le_of_dvd hc (orderOf_map_dvd P.weylGroupToPerm c))⟩, by rw [map_pow, heq]⟩

section FiniteType

variable (b : P.Base) (hft : IsFiniteType b.cartanMatrix)
  (hconn : (diagramGraph b.cartanMatrix).Preconnected)
include hft hconn

private theorem subsingleton_fin_pow_mem_inversions_bipartite_of_isFiniteType
    [Nontrivial b.support] (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) (j : ι)
    {m₁ m₂ : Fin (orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement col))}
    (hm₁ : P.weylGroupToPerm ((weylCoxeterSystem P b).bipartiteCoxeterElement col ^ (m₁ : ℕ)) j ∈
      inversions P b ((weylCoxeterSystem P b).bipartiteCoxeterElement col))
    (hm₂ : P.weylGroupToPerm ((weylCoxeterSystem P b).bipartiteCoxeterElement col ^ (m₂ : ℕ)) j ∈
      inversions P b ((weylCoxeterSystem P b).bipartiteCoxeterElement col)) :
    m₁ = m₂ := by
  have := P.finite_weylGroup_of_base b; classical
  let c₀ := (weylCoxeterSystem P b).bipartiteCoxeterElement col; let h := orderOf c₀
  obtain ⟨e₁, e₂, -, -, -, hWinv_pow, hsector⟩ :=
    b.exists_coxeterPlane_bipartiteCoxeterElement_of_isFiniteType hft hconn col
  have hh_pos : (0 : ℝ) < h := Nat.cast_pos.mpr (orderOf_pos c₀); set φ₀ : ℝ := Real.pi / (2 * h)
  have hy₀ := hsector φ₀ (by positivity)
    ((div_lt_div_iff₀ (by positivity) hh_pos).mpr (by nlinarith [Real.pi_pos]))
  set z : ℂ := ⟨b.corootEval ℝ j e₁, b.corootEval ℝ j e₂⟩
  have hcos_formula (φ : ℝ) :
      b.corootEval ℝ j (Real.cos φ • e₁ + Real.sin φ • e₂) = ‖z‖ * Real.cos (φ - z.arg) := by
    rw [Real.cos_sub, mul_add, mul_left_comm ‖z‖, Complex.norm_mul_cos_arg,
      mul_left_comm ‖z‖, Complex.norm_mul_sin_arg]; simp [z]
  have hisPos_iff (k : ℕ) : b.IsPos (P.weylGroupToPerm (c₀ ^ k) j) ↔
      0 < Real.cos (φ₀ - z.arg + 2 * Real.pi * k / h) := by
    have heq := b.corootEval_weylGroupToPerm_inv ((b.actsBy_bipartiteCoxeterElement_inv col).pow k)
      ℝ j (Real.cos φ₀ • e₁ + Real.sin φ₀ • e₂)
    rw [inv_pow, inv_inv, Matrix.map_pow, hWinv_pow k φ₀, hcos_formula, add_sub_right_comm] at heq
    rw [← mem_posRoots, ← b.corootEval_pos_iff_mem_posRoots hy₀, heq]
    exact mul_pos_iff_of_pos_left ((norm_nonneg z).lt_of_ne' fun h0 ↦
      b.corootEval_ne_zero_of_forall_pos hy₀ j (by rw [hcos_formula φ₀, h0, zero_mul]))
  have hstep (m : Fin h) (hm : P.weylGroupToPerm (c₀ ^ (m : ℕ)) j ∈ inversions P b c₀) :
      0 < Real.cos (φ₀ - z.arg + 2 * Real.pi * (m : ℝ) / h) ∧
        Real.cos (φ₀ - z.arg + 2 * Real.pi * ((m : ℝ) + 1) / h) ≤ 0 := by
    obtain ⟨hp, hn⟩ := (mem_inversions P b c₀ _).mp hm
    rw [← Equiv.Perm.mul_apply, ← map_mul, ← pow_succ', hisPos_iff] at hn
    exact ⟨(hisPos_iff m).mp hp, by push_cast at hn; exact not_lt.mp hn⟩
  exact Real.eq_of_cos_pos_of_cos_add_one_nonpos
    (hstep m₁ hm₁).1 (hstep m₁ hm₁).2 (hstep m₂ hm₂).1 (hstep m₂ hm₂).2

private theorem card_quotient_sameCycle_bipartite_of_isFiniteType
    [Nontrivial b.support] (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid
      (P.weylGroupToPerm ((weylCoxeterSystem P b).bipartiteCoxeterElement col)))) =
      b.support.card := by
  have := P.finite_weylGroup_of_base b; classical
  obtain ⟨_, _, -, -, hnd₀, hall₀, hword₀⟩ :=
    (weylCoxeterSystem P b).exists_wordProd_eq_bipartiteCoxeterElement col
  set c₀ := (weylCoxeterSystem P b).bipartiteCoxeterElement col
  rw [weylCoxeterSystem_wordProd] at hword₀
  rw [← Nat.card_eq_of_bijective (fun k : inversions P b c₀ ↦
      Quotient.mk (Equiv.Perm.SameCycle.setoid (P.weylGroupToPerm c₀)) k.val)
    ⟨fun k₁ k₂ hk ↦ Subtype.ext <| by
      obtain ⟨m, hm⟩ := exists_fin_pow_eq_of_sameCycle (orderOf_pos c₀) (Quotient.exact hk)
      have hm0 : m = ⟨0, orderOf_pos c₀⟩ :=
        (b.subsingleton_fin_pow_mem_inversions_bipartite_of_isFiniteType hft hconn col k₁.val
          (m₁ := ⟨0, orderOf_pos c₀⟩) (m₂ := m) (by simp) (hm ▸ k₂.property)).symm
      rwa [hm0, Fin.val_mk, pow_zero, map_one, Equiv.Perm.one_apply] at hm,
      hword₀ ▸ b.surjective_quotientMk_inversions_wordProd hnd₀ hall₀⟩,
    Nat.card_coe_set_eq, ncard_inversions_bipartiteCoxeterElement]

variable {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
include hnd hall

/-- **Steinberg's freeness of Coxeter orbits on roots** (Cartan-matrix form): when `b.cartanMatrix`
is of finite type with preconnected Dynkin diagram, for any Coxeter element `c = wordProd P b l`
and root index `j : ι`, the power `c ^ k` fixes `j` if and only if `orderOf c ∣ k`. -/
theorem weylGroupToPerm_wordProd_pow_apply_eq_self_iff_of_isFiniteType (j : ι) (k : ℕ) :
    P.weylGroupToPerm (wordProd P b l ^ k) j = j ↔ orderOf (wordProd P b l) ∣ k := by
  refine ⟨fun hfix ↦ ?_, fun h ↦ by rw [orderOf_dvd_iff_pow_eq_one.mp h, map_one]; rfl⟩
  classical
  have : Nonempty ι := ⟨j⟩; have hW := b.actsBy_wordProd l
  obtain ⟨z, -, hz_eig, hz_prim, hz_reg, -⟩ :=
    b.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd_of_isFiniteType hft hconn hnd hall hW
  have heval := b.corootEval_weylGroupToPerm_inv (hW.pow k) ℂ j z
  rw [map_inv, Equiv.Perm.inv_eq_iff_eq.mpr hfix.symm, Matrix.map_pow,
    Matrix.pow_mulVec_eq_pow_smul hz_eig k, map_smul, smul_eq_mul] at heval
  exact hz_prim.dvd_of_pow_eq_one k (mul_right_cancel₀ (hz_reg j) (by linear_combination -heval))

/-- Every root index `j : ι` has minimal period `orderOf (wordProd P b l)` under `wordProd P b l`
when `b.cartanMatrix` is of finite type with preconnected Dynkin diagram. -/
theorem minimalPeriod_weylGroupToPerm_wordProd_of_isFiniteType (j : ι) :
    Function.minimalPeriod (P.weylGroupToPerm (wordProd P b l)) j = orderOf (wordProd P b l) := by
  have := P.finite_weylGroup_of_base b; set σ := P.weylGroupToPerm (wordProd P b l)
  refine Nat.dvd_antisymm (Function.IsPeriodicPt.minimalPeriod_dvd <| by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow, ← map_pow,
      pow_orderOf_eq_one, map_one]; rfl) ?_
  rw [← b.weylGroupToPerm_wordProd_pow_apply_eq_self_iff_of_isFiniteType hft hconn hnd hall j]
  simpa only [σ, Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow, ← map_pow] using
    Function.isPeriodicPt_minimalPeriod σ j

/-- Every `⟨wordProd P b l⟩`-orbit on the root indices has cardinality `orderOf (wordProd P b l)`
when `b.cartanMatrix` is of finite type with preconnected Dynkin diagram. -/
theorem ncard_setOf_sameCycle_weylGroupToPerm_wordProd_of_isFiniteType (j : ι) :
    {k : ι | Equiv.Perm.SameCycle (P.weylGroupToPerm (wordProd P b l)) j k}.ncard =
      orderOf (wordProd P b l) :=
  (Equiv.Perm.ncard_setOf_sameCycle _ _).trans
    (b.minimalPeriod_weylGroupToPerm_wordProd_of_isFiniteType hft hconn hnd hall j)

private theorem natCard_eq_card_quotient_mul_orderOf_wordProd :
    Nat.card ι = Nat.card (Quotient (Equiv.Perm.SameCycle.setoid
      (P.weylGroupToPerm (wordProd P b l)))) * orderOf (wordProd P b l) := by
  let := Fintype.ofFinite ι; classical
  simpa only [Finset.sum_const, Finset.card_univ, Finset.card_range, smul_eq_mul, mul_one,
    Nat.card_eq_fintype_card,
    b.minimalPeriod_weylGroupToPerm_wordProd_of_isFiniteType hft hconn hnd hall] using
    (Equiv.Perm.sum_quotient_sameCycle_sum_range
      (P.weylGroupToPerm (wordProd P b l)) fun _ ↦ (1 : ℕ)).symm

private theorem natCard_eq_card_support_mul_orderOf_wordProd_subsingleton [Subsingleton b.support] :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) := by
  let := Fintype.ofFinite ι; by_cases hne : Nonempty b.support
  · obtain ⟨i₀⟩ := hne; set c := wordProd P b l with hc
    have hword_pow (lw : List b.support) : wordProd P b lw = c ^ lw.length :=
      lw.rec (by simp) fun a lw ih ↦ by
        rw [wordProd_cons, ih, Subsingleton.elim a i₀, List.length_cons, pow_succ', hc,
          hnd.eq_singleton_of_mem (hall i₀), wordProd_cons, wordProd_nil, mul_one]
    have hncard := b.ncard_setOf_sameCycle_weylGroupToPerm_wordProd_of_isFiniteType hft hconn
      hnd hall (i₀ : ι)
    rw [show {k : ι | Equiv.Perm.SameCycle (P.weylGroupToPerm c) (i₀ : ι) k} = Set.univ from
        Set.eq_univ_of_forall fun j ↦ by
          obtain ⟨i, hi, w, rfl⟩ := exists_mem_support_weylGroupToPerm_eq b j
          obtain ⟨lw, -, hw⟩ := (weylCoxeterSystem P b).exists_isReduced w
          exact ⟨lw.length, by rw [zpow_natCast, ← map_pow, ← hword_pow lw,
            ← weylCoxeterSystem_wordProd, hw, Subtype.ext_iff.mp (Subsingleton.elim i₀ ⟨i, hi⟩)]⟩,
      Set.ncard_univ] at hncard
    rw [← Fintype.card_coe, Fintype.card_eq_one_iff.mpr ⟨i₀, (Subsingleton.elim · i₀)⟩,
      one_mul, hncard]
  · have : IsEmpty ι := ⟨fun j ↦ let ⟨i, hi, _, _⟩ := exists_mem_support_weylGroupToPerm_eq b j
      hne ⟨⟨i, hi⟩⟩⟩
    simp [Nat.card_eq_fintype_card, ← Fintype.card_coe]

/-- **Bourbaki's root-count formula `|Φ| = r · h`** (Cartan-matrix form): when `b.cartanMatrix` is
of finite type with preconnected Dynkin diagram, the number of roots equals `b.support.card` times
the order of any Coxeter element `wordProd P b l` (requiring neither spanning nor irreducibility
over `R`). -/
theorem natCard_eq_card_support_mul_orderOf_wordProd_of_isFiniteType :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) := by
  classical
  exact (subsingleton_or_nontrivial b.support).elim
    (fun _ ↦ b.natCard_eq_card_support_mul_orderOf_wordProd_subsingleton hft hconn hnd hall)
    fun _ ↦ by
      obtain ⟨col⟩ := nonempty_coloring_graph_coxeterMatrixOfBase_of_isFiniteType P b hft
      obtain ⟨_, _, -, -, hnd₀, hall₀, hword₀⟩ :=
        (weylCoxeterSystem P b).exists_wordProd_eq_bipartiteCoxeterElement col
      have hu := (weylCoxeterSystem P b).isConj_wordProd_bipartiteCoxeterElement
        (isAcyclic_graph_coxeterMatrixOfBase_of_isFiniteType P b hft) col hnd hall
      rw [weylCoxeterSystem_wordProd] at hword₀ hu
      rw [b.natCard_eq_card_quotient_mul_orderOf_wordProd hft hconn hnd₀ hall₀, hword₀,
        b.card_quotient_sameCycle_bipartite_of_isFiniteType hft hconn col,
        hu.choose_spec.orderOf_eq]

/-- **Positive-root count formula `2 |Φ⁺| = r · h`** (Cartan-matrix form): when `b.cartanMatrix`
is of finite type with preconnected Dynkin diagram, twice the number of positive roots equals
`b.support.card * orderOf (wordProd P b l)`. -/
theorem two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd_of_isFiniteType :
    2 * (posRoots P b).ncard = b.support.card * orderOf (wordProd P b l) :=
  (two_mul_ncard_posRoots P b).trans
    (b.natCard_eq_card_support_mul_orderOf_wordProd_of_isFiniteType hft hconn hnd hall)

/-- **Positive-root count formula `|Φ⁺| = r · h / 2`** (Cartan-matrix form). -/
theorem ncard_posRoots_eq_card_support_mul_orderOf_wordProd_div_two_of_isFiniteType :
    (posRoots P b).ncard = b.support.card * orderOf (wordProd P b l) / 2 := by
  rw [ncard_posRoots_eq_natCard_div_two,
    b.natCard_eq_card_support_mul_orderOf_wordProd_of_isFiniteType hft hconn hnd hall]

/-- **Number of Coxeter orbits on roots** (Cartan-matrix form): when `b.cartanMatrix` is of finite
type with preconnected Dynkin diagram, every Coxeter element `wordProd P b l` partitions `ι` into
`b.support.card` cyclic orbits. -/
theorem card_quotient_sameCycle_weylGroupToPerm_wordProd_of_isFiniteType :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (P.weylGroupToPerm (wordProd P b l)))) =
      b.support.card :=
  have := P.finite_weylGroup_of_base b
  Nat.mul_right_cancel (orderOf_pos (wordProd P b l)) <|
    (b.natCard_eq_card_quotient_mul_orderOf_wordProd hft hconn hnd hall).symm.trans
      (b.natCard_eq_card_support_mul_orderOf_wordProd_of_isFiniteType hft hconn hnd hall)

/-- **Steinberg's unique inversion per Coxeter orbit** (Cartan-matrix form): when `b.cartanMatrix`
is of finite type with preconnected Dynkin diagram, for any Coxeter element `c = wordProd P b l`
and any root index `j : ι`, the `⟨c⟩`-orbit of `j` contains a unique root index in
`inversions P b c`. -/
theorem existsUnique_sameCycle_mem_inversions_wordProd_of_isFiniteType (j : ι) :
    ∃! k : ι, Equiv.Perm.SameCycle (P.weylGroupToPerm (wordProd P b l)) j k ∧
      k ∈ inversions P b (wordProd P b l) := by
  have hbij : Function.Bijective (fun k : inversions P b (wordProd P b l) ↦
      Quotient.mk (Equiv.Perm.SameCycle.setoid (P.weylGroupToPerm (wordProd P b l))) k.val) :=
    (Nat.bijective_iff_surjective_and_card _).mpr ⟨b.surjective_quotientMk_inversions_wordProd
      hnd hall, by rw [Nat.card_coe_set_eq, ncard_inversions_wordProd_eq_card_support P b hnd hall,
        b.card_quotient_sameCycle_weylGroupToPerm_wordProd_of_isFiniteType hft hconn hnd hall]⟩
  obtain ⟨⟨k, hk_inv⟩, hk_eq⟩ := hbij.surjective ⟦j⟧
  exact ⟨k, ⟨(Quotient.exact hk_eq).symm, hk_inv⟩, fun y ⟨hy_sc, hy_inv⟩ ↦ congrArg Subtype.val <|
    hbij.injective (a₁ := ⟨y, hy_inv⟩) (a₂ := ⟨k, hk_inv⟩)
      ((Quotient.sound hy_sc.symm).trans hk_eq.symm)⟩

/-- For any Coxeter element `c = wordProd P b l` (with `b.cartanMatrix` of finite type and
preconnected Dynkin diagram) and any root index `j : ι`, a unique `m : Fin (orderOf c)` sends `j`
under `P.weylGroupToPerm (c ^ (m : ℕ))` into `inversions P b c`. -/
theorem existsUnique_pow_mem_inversions_wordProd_of_isFiniteType (j : ι) :
    ∃! m : Fin (orderOf (wordProd P b l)),
      P.weylGroupToPerm (wordProd P b l ^ (m : ℕ)) j ∈ inversions P b (wordProd P b l) := by
  have := P.finite_weylGroup_of_base b; set c := wordProd P b l
  obtain ⟨k, ⟨hk_sc, hk_inv⟩, hk_uniq⟩ :=
    b.existsUnique_sameCycle_mem_inversions_wordProd_of_isFiniteType hft hconn hnd hall j
  obtain ⟨m₀, hm₀⟩ := exists_fin_pow_eq_of_sameCycle (orderOf_pos c) hk_sc
  have hper := (b.minimalPeriod_weylGroupToPerm_wordProd_of_isFiniteType hft hconn hnd hall j).symm
  refine ⟨m₀, by rwa [← hm₀] at hk_inv, fun m hm ↦ Fin.ext <|
    (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (lt_of_lt_of_eq m.isLt hper)
      (lt_of_lt_of_eq m₀.isLt hper)).mp (by simpa only [← Equiv.Perm.coe_pow, ← map_pow] using
        (hk_uniq _ ⟨⟨(m : ℤ), by rw [zpow_natCast, map_pow]⟩, hm⟩).trans hm₀.symm)⟩

end FiniteType

section Irreducible

variable [P.IsIrreducible] (b : P.Base) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
include hnd hall

/-- **Steinberg's freeness of Coxeter orbits on roots.** For any Coxeter element
`c = wordProd P b l` of an irreducible finite crystallographic reduced root pairing and any root
index `j : ι`, the power `c ^ k` fixes `j` if and only if `orderOf c ∣ k`. -/
theorem weylGroupToPerm_wordProd_pow_apply_eq_self_iff (j : ι) (k : ℕ) :
    P.weylGroupToPerm (wordProd P b l ^ k) j = j ↔ orderOf (wordProd P b l) ∣ k :=
  have : Nonempty ι := ⟨j⟩; have : NeZero (2 : R) := ⟨by norm_num⟩
  b.weylGroupToPerm_wordProd_pow_apply_eq_self_iff_of_isFiniteType
    (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall j k

/-- Every root index `j : ι` has minimal period `orderOf (wordProd P b l)` under a Coxeter element
`wordProd P b l`. -/
theorem minimalPeriod_weylGroupToPerm_wordProd (j : ι) :
    Function.minimalPeriod (P.weylGroupToPerm (wordProd P b l)) j = orderOf (wordProd P b l) :=
  have : Nonempty ι := ⟨j⟩; have : NeZero (2 : R) := ⟨by norm_num⟩
  b.minimalPeriod_weylGroupToPerm_wordProd_of_isFiniteType
    (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall j

/-- Every `⟨wordProd P b l⟩`-orbit of a root index has cardinality `orderOf (wordProd P b l)`. -/
theorem ncard_setOf_sameCycle_weylGroupToPerm_wordProd (j : ι) :
    {k : ι | Equiv.Perm.SameCycle (P.weylGroupToPerm (wordProd P b l)) j k}.ncard =
      orderOf (wordProd P b l) :=
  (Equiv.Perm.ncard_setOf_sameCycle _ _).trans (b.minimalPeriod_weylGroupToPerm_wordProd hnd hall j)

/-- **Positive-root count formula `|Φ⁺| = r · h / 2`.** -/
theorem ncard_posRoots_eq_card_support_mul_orderOf_wordProd_div_two :
    (posRoots P b).ncard = b.support.card * orderOf (wordProd P b l) / 2 := by
  by_cases hne : Nonempty ι
  · have : NeZero (2 : R) := ⟨by norm_num⟩
    exact b.ncard_posRoots_eq_card_support_mul_orderOf_wordProd_div_two_of_isFiniteType
      (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall
  · have : IsEmpty ι := not_nonempty_iff.mp hne
    simp [Set.eq_empty_iff_forall_notMem.mpr fun x _ ↦ IsEmpty.false x,
      Finset.eq_empty_iff_forall_notMem.mpr fun x _ ↦ IsEmpty.false x]

/-- **Number of Coxeter orbits on roots.** Every Coxeter element `wordProd P b l` partitions the
root indices `ι` into `b.support.card` cyclic orbits. -/
theorem card_quotient_sameCycle_weylGroupToPerm_wordProd :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (P.weylGroupToPerm (wordProd P b l)))) =
      b.support.card := by
  by_cases hne : Nonempty ι
  · have : NeZero (2 : R) := ⟨by norm_num⟩
    exact b.card_quotient_sameCycle_weylGroupToPerm_wordProd_of_isFiniteType
      (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall
  · have : IsEmpty ι := not_nonempty_iff.mp hne
    have : IsEmpty (Quotient (Equiv.Perm.SameCycle.setoid
        (P.weylGroupToPerm (wordProd P b l)))) := ⟨Quotient.ind IsEmpty.false⟩
    simp [Finset.eq_empty_iff_forall_notMem.mpr fun x _ ↦ IsEmpty.false x]

/-- **Steinberg's unique inversion per Coxeter orbit.** For any Coxeter element
`c = wordProd P b l` and any root index `j : ι`, the `⟨c⟩`-orbit of `j` contains a unique root
index in `inversions P b c`. -/
theorem existsUnique_sameCycle_mem_inversions_wordProd (j : ι) :
    ∃! k : ι, Equiv.Perm.SameCycle (P.weylGroupToPerm (wordProd P b l)) j k ∧
      k ∈ inversions P b (wordProd P b l) :=
  have : Nonempty ι := ⟨j⟩; have : NeZero (2 : R) := ⟨by norm_num⟩
  b.existsUnique_sameCycle_mem_inversions_wordProd_of_isFiniteType
    (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall j

/-- For any Coxeter element `c = wordProd P b l` and any root index `j : ι`, a unique
`m : Fin (orderOf c)` sends `j` under `P.weylGroupToPerm (c ^ (m : ℕ))` into `inversions P b c`. -/
theorem existsUnique_pow_mem_inversions_wordProd (j : ι) :
    ∃! m : Fin (orderOf (wordProd P b l)),
      P.weylGroupToPerm (wordProd P b l ^ (m : ℕ)) j ∈ inversions P b (wordProd P b l) :=
  have : Nonempty ι := ⟨j⟩; have : NeZero (2 : R) := ⟨by norm_num⟩
  b.existsUnique_pow_mem_inversions_wordProd_of_isFiniteType
    (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall j

end Irreducible

end Orbits

end RootPairing.Base

namespace TauCeti

open RootPairing

variable {ι R M N : Type*} [CommRing R] [CharZero R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [Finite ι] [P.IsRootSystem]
  (b : P.Base)

/-- Along the orbit of a root under a Weyl-group element fixing no nonzero vector, the heights over
a period add up to zero: the sum of the roots over a period is a fixed vector. -/
private theorem sum_range_height_weylGroupToPerm_pow_eq_zero {w : P.weylGroup}
    (hw : ∀ y : M, w • y = y → y = 0) (j : ι) :
    ∑ k ∈ Finset.range (orderOf w), b.height (P.weylGroupToPerm (w ^ k) j) = 0 := by
  have := P.finite_weylGroup
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (orderOf_pos w).ne'
  -- The sum of the roots over a period is fixed by `w`, hence zero.
  have hfix : ∑ k ∈ Finset.range (orderOf w), (w ^ k) • P.root j = 0 := by
    refine hw _ ?_
    rw [Finset.smul_sum, hn, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [← mul_smul, ← pow_succ', ← hn, pow_orderOf_eq_one, pow_zero]
  have hheight := congrArg (heightLinearMap P b) hfix
  simp only [map_sum, P.weylGroup_apply_root, heightLinearMap_root, map_zero] at hheight
  exact_mod_cast hheight

/-- **Every orbit of a fixed-point-free Weyl-group element meets its inversion set.** If `w` fixes
no nonzero vector, then for every root `j` some `w ^ k j` with `k < orderOf w` is a positive root
that `w` sends to a negative root. -/
theorem exists_lt_orderOf_weylGroupToPerm_pow_mem_inversions {w : P.weylGroup}
    (hw : ∀ y : M, w • y = y → y = 0) (j : ι) :
    ∃ k < orderOf w, P.weylGroupToPerm (w ^ k) j ∈ inversions P b w := by
  have := P.finite_weylGroup
  have hpos := orderOf_pos w
  set a : ℕ → ι := fun k ↦ P.weylGroupToPerm (w ^ k) j with ha
  have hmod (k : ℕ) : a (k % orderOf w) = a k := by simp only [ha, pow_mod_orderOf]
  have hsucc (k : ℕ) : a (k + 1) = P.weylGroupToPerm w (a k) := by
    simp only [ha, pow_succ', map_mul, Equiv.Perm.mul_apply]
  have hper (k : ℕ) : a (k + orderOf w) = a k := by
    simp only [ha, pow_add, pow_orderOf_eq_one, mul_one]
  by_contra! hno
  replace hno : ∀ k < orderOf w, a k ∉ inversions P b w := hno
  -- Positivity propagates along the orbit, since no step goes from positive to negative.
  have hstep (k : ℕ) (hk : b.IsPos (a k)) : b.IsPos (a (k + 1)) := by
    have := hno (k % orderOf w) (Nat.mod_lt _ hpos)
    rw [mem_inversions, hmod] at this
    rw [hsucc]
    by_contra h
    exact this ⟨hk, h⟩
  have hsum := sum_range_height_weylGroupToPerm_pow_eq_zero b hw j
  by_cases hex : ∃ p, b.IsPos (a p)
  · -- Then every root of the orbit is positive, and the heights add up to a positive number.
    obtain ⟨p, hp⟩ := hex
    have hall (t : ℕ) : b.IsPos (a (p % orderOf w + t)) := by
      induction t with
      | zero => rwa [add_zero, hmod]
      | succ t ih => exact hstep _ ih
    refine (Finset.sum_pos (fun k _ ↦ ?_) (Finset.nonempty_range_iff.mpr hpos.ne')).ne' hsum
    have hidx : p % orderOf w + (k + orderOf w - p % orderOf w) = k + orderOf w := by
      have := Nat.mod_lt p hpos
      omega
    have hk := hall (k + orderOf w - p % orderOf w)
    rw [hidx, hper] at hk
    exact one_le_height_of_mem_posRoots P b ((mem_posRoots P b _).2 hk)
  · -- Otherwise every root of the orbit is negative, and the heights add up to a negative number.
    push Not at hex
    exact (Finset.sum_neg
      (fun k _ ↦ height_neg_of_mem_negRoots P b ((mem_negRoots P b _).2 (hex k)))
      (Finset.nonempty_range_iff.mpr hpos.ne')).ne hsum

/-- **A fixed-point-free Weyl-group element has at most `orderOf w` roots per inversion.** If `w`
fixes no nonzero vector, then the number of roots is at most `orderOf w` times the number of
positive roots that `w` sends to negative roots. -/
theorem natCard_le_orderOf_mul_ncard_inversions {w : P.weylGroup}
    (hw : ∀ y : M, w • y = y → y = 0) :
    Nat.card ι ≤ orderOf w * (inversions P b w).ncard := by
  choose k hk hkinv using exists_lt_orderOf_weylGroupToPerm_pow_mem_inversions b hw
  let F : ι → Fin (orderOf w) × inversions P b w := fun j ↦ (⟨k j, hk j⟩, ⟨_, hkinv j⟩)
  have hF : Function.Injective F := fun j j' hjj' ↦ by
    simp only [F, Prod.mk.injEq, Fin.mk.injEq, Subtype.mk.injEq] at hjj'
    rw [← hjj'.1] at hjj'
    exact (P.weylGroupToPerm (w ^ k j)).injective hjj'.2
  rw [← Nat.card_coe_set_eq, ← Nat.card_fin (orderOf w), ← Nat.card_prod]
  exact Nat.card_le_card_of_injective F hF

variable [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- **A root system has at most `r * orderOf c` roots, for a Coxeter element `c`.** For a base of
a finite reduced crystallographic root system, a word using every simple reflection exactly once
spells an element `c` such that the number of roots is at most `orderOf c` times the length of the
word. -/
theorem natCard_le_orderOf_wordProd_mul_length {l : List b.support} (hl : l.Nodup)
    (hl' : ∀ i, i ∈ l) :
    Nat.card ι ≤ orderOf (wordProd P b l) * l.length :=
  (natCard_le_orderOf_mul_ncard_inversions b fun _ hy ↦
    (wordProd_smul_eq_self_iff_eq_zero b hl hl').mp hy).trans
    (Nat.mul_le_mul_left _ (ncard_inversions_wordProd_le_length P b l))

end TauCeti

end
