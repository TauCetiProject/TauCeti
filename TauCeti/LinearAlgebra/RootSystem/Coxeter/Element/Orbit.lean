/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Angle
import TauCeti.Data.List.Pairwise
import TauCeti.GroupTheory.Coxeter.CoxeterElement
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.Cycle.Enumeration
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Plane
import TauCeti.LinearAlgebra.RootSystem.Coxeter.FixedPoints
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Length
import TauCeti.LinearAlgebra.RootSystem.LongestElement
import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Basic

/-!
# Steinberg's Coxeter orbits on roots and the root-count formula `|Φ| = r · h`

For an irreducible, finite, reduced, crystallographic root pairing `P` with base `b` of rank
`r = b.support.card` (or when `b.cartanMatrix` is of finite type with preconnected Dynkin diagram)
and any Coxeter element `c = wordProd P b l` of order `h = orderOf c`, we prove Steinberg's
root-orbit theorem and Bourbaki's root-count formula without assuming root spanning:
1. **Free cyclic orbits** (`weylGroupToPerm_wordProd_pow_apply_eq_self_iff`,
   `minimalPeriod_weylGroupToPerm_wordProd`, `ncard_setOf_sameCycle_weylGroupToPerm_wordProd`):
   every `⟨c⟩`-orbit on `ι` has minimal period and cardinality `h`.
2. **Unique inversion per orbit, `|Φ| = r · h`, and `|Φ⁺| = r · h / 2`**
   (`card_quotient_sameCycle_weylGroupToPerm_wordProd`,
   `existsUnique_sameCycle_mem_inversions_wordProd`, `existsUnique_pow_mem_inversions_wordProd`,
   `natCard_eq_card_support_mul_orderOf_wordProd`,
   `ncard_posRoots_eq_card_support_mul_orderOf_wordProd_div_two`): `⟨c⟩` partitions `ι` into `r`
   cyclic orbits, each containing a unique index in `inversions P b c`.

Every theorem is first proved in an `_of_isFiniteType` Cartan-matrix form (`IsFiniteType` and
preconnected diagram), allowing downstream applications (such as exceptional root counts in
`TauCeti.LinearAlgebra.RootSystem.NumberOfRoots.Exceptional`) directly from `HasCartanType`
without `[P.IsIrreducible]`.

## References
* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. **91** (1959), 493–504.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2; Ch. VI, §1, no. 11;
  J. E. Humphreys, *Reflection Groups and Coxeter Groups*, §§ 3.16–3.18.
-/

public section

open Matrix RootPairing TauCeti

/-! ### Free Coxeter orbits on roots and `|Φ| = r · h` -/

namespace RootPairing.Base

section Orbits

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

private theorem exists_sameCycle_mem_inversions_wordProd (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) (j : ι) :
    ∃ k : ι, Equiv.Perm.SameCycle (P.weylGroupToPerm (wordProd P b l)) j k ∧
      k ∈ inversions P b (wordProd P b l) := by
  set c := wordProd P b l; set σ := P.weylGroupToPerm c
  have hσ : (c : P.Aut).indexEquiv = σ :=
    _root_.Equiv.ext fun i ↦ (P.weylGroupToPerm_apply c i).symm
  have hw₀ : longestElement P b • ∑ y ∈ P.orbitIndices (c : P.Aut) j, P.root y =
      ∑ y ∈ P.orbitIndices (c : P.Aut) j, P.root y :=
    (wordProd_smul_eq_self_iff_forall_smul_eq_self b hnd hall).mp
      (by rw [← P.orbitSum_def]; exact P.weightMap_orbitSum_self (c : P.Aut) j) (longestElement P b)
  obtain ⟨⟨y₁, hy₁O, hy₁_pos⟩, ⟨y₂, hy₂O, hy₂_neg⟩⟩ :=
    exists_isPos_and_not_isPos_of_longestElement_smul_sum_eq_self
      (P.orbitIndices_nonempty (c : P.Aut) j) hw₀
  have hsc₁ : Equiv.Perm.SameCycle σ j y₁ := hσ ▸ P.mem_orbitIndices.mp hy₁O
  obtain ⟨n, hn⟩ := (hsc₁.symm.trans (hσ ▸ P.mem_orbitIndices.mp hy₂O)).exists_nat_pow_eq
  clear hy₂O; induction n generalizing y₂ with
  | zero => exact (hy₂_neg (hn ▸ hy₁_pos)).elim
  | succ n ih =>
    by_cases hmid : b.IsPos ((σ ^ n) y₁)
    · refine ⟨(σ ^ n) y₁, hsc₁.trans ⟨n, by simp⟩, (mem_inversions P b c _).mpr ⟨hmid, ?_⟩⟩
      rwa [← Equiv.Perm.mul_apply, ← pow_succ', hn]
    · exact ih ((σ ^ n) y₁) hmid rfl

private theorem surjective_quotientMk_inversions_wordProd (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    Function.Surjective fun k : inversions P b (wordProd P b l) ↦
      Quotient.mk (Equiv.Perm.SameCycle.setoid (P.weylGroupToPerm (wordProd P b l))) k.val :=
  Quotient.ind fun j ↦
    let ⟨k, hsc, hinv⟩ := b.exists_sameCycle_mem_inversions_wordProd hnd hall j
    ⟨⟨k, hinv⟩, Quotient.sound hsc.symm⟩

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
  have hy₀ := hsector φ₀ (div_pos Real.pi_pos (by positivity))
    ((div_lt_div_iff₀ (by positivity) hh_pos).mpr (by nlinarith [Real.pi_pos]))
  set z : ℂ := ⟨b.corootEval ℝ j e₁, b.corootEval ℝ j e₂⟩
  have hcos_formula (φ : ℝ) :
      b.corootEval ℝ j (Real.cos φ • e₁ + Real.sin φ • e₂) = ‖z‖ * Real.cos (φ - z.arg) := by
    rw [Real.cos_sub, mul_add, mul_left_comm (‖z‖), Complex.norm_mul_cos_arg,
      mul_left_comm (‖z‖), Complex.norm_mul_sin_arg]; simp [z]
  have hnorm_pos : 0 < ‖z‖ := (norm_nonneg z).lt_of_ne' fun h0 ↦
    b.corootEval_ne_zero_of_forall_pos hy₀ j (by rw [hcos_formula φ₀, h0, zero_mul])
  have hisPos_iff (k : ℕ) : b.IsPos (P.weylGroupToPerm (c₀ ^ k) j) ↔
      0 < Real.cos (φ₀ - z.arg + 2 * Real.pi * k / h) := by
    rw [← mem_posRoots, ← b.corootEval_pos_iff_mem_posRoots hy₀]
    have heq := b.corootEval_weylGroupToPerm_inv
      ((b.actsBy_bipartiteCoxeterElement_inv col).pow k) ℝ j (Real.cos φ₀ • e₁ + Real.sin φ₀ • e₂)
    rw [inv_pow, inv_inv, Matrix.map_pow, hWinv_pow k φ₀, hcos_formula] at heq
    have hangle : φ₀ + 2 * Real.pi * k / h - z.arg = φ₀ - z.arg + 2 * Real.pi * k / h := by ring
    rw [heq, hangle]; exact mul_pos_iff_of_pos_left hnorm_pos
  have hstep (m : Fin h) (hm : P.weylGroupToPerm (c₀ ^ (m : ℕ)) j ∈ inversions P b c₀) :
      0 < Real.cos (φ₀ - z.arg + 2 * Real.pi * (m : ℝ) / h) ∧
        Real.cos (φ₀ - z.arg + 2 * Real.pi * ((m : ℝ) + 1) / h) ≤ 0 := by
    obtain ⟨hp, hn⟩ := (mem_inversions P b c₀ _).mp hm
    rw [← Equiv.Perm.mul_apply, ← map_mul, ← pow_succ'] at hn; rw [hisPos_iff] at hp hn
    exact ⟨hp, not_lt.mp (by push_cast at hn; exact hn)⟩
  exact eq_of_cos_pos_of_cos_add_one_nonpos
    (hstep m₁ hm₁).1 (hstep m₁ hm₁).2 (hstep m₂ hm₂).1 (hstep m₂ hm₂).2

private theorem card_quotient_sameCycle_bipartite_of_isFiniteType
    [Nontrivial b.support] (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid
      (P.weylGroupToPerm ((weylCoxeterSystem P b).bipartiteCoxeterElement col)))) =
      b.support.card := by
  have := P.finite_weylGroup_of_base b; classical
  obtain ⟨l₁, l₂, -, -, hnd₀, hall₀, hword₀⟩ :=
    (weylCoxeterSystem P b).exists_wordProd_eq_bipartiteCoxeterElement col
  rw [weylCoxeterSystem_wordProd] at hword₀
  let c₀ := (weylCoxeterSystem P b).bipartiteCoxeterElement col
  let f : inversions P b c₀ → Quotient (Equiv.Perm.SameCycle.setoid (P.weylGroupToPerm c₀)) :=
    fun k ↦ Quotient.mk _ k.val
  have hsurj : Function.Surjective f := by
    dsimp only [f, c₀]; rw [← hword₀]; exact b.surjective_quotientMk_inversions_wordProd hnd₀ hall₀
  have hinj : Function.Injective f := fun k₁ k₂ hk ↦ by
    obtain ⟨n, hn⟩ := (Quotient.exact hk).exists_nat_pow_eq
    let m₁ : Fin (orderOf c₀) := ⟨0, orderOf_pos c₀⟩
    let m₂ : Fin (orderOf c₀) := ⟨n % orderOf c₀, Nat.mod_lt n (orderOf_pos c₀)⟩
    have hm₁ : P.weylGroupToPerm (c₀ ^ (m₁ : ℕ)) k₁.val ∈ inversions P b c₀ := by simp [m₁]
    have hm₂ : P.weylGroupToPerm (c₀ ^ (m₂ : ℕ)) k₁.val ∈ inversions P b c₀ := by
      dsimp only [m₂]; rw [pow_mod_orderOf, map_pow, hn]; exact k₂.property
    have hmod : 0 = n % orderOf c₀ := congrArg Fin.val
      (b.subsingleton_fin_pow_mem_inversions_bipartite_of_isFiniteType hft hconn col k₁.val hm₁ hm₂)
    exact Subtype.ext (by rw [← hn, ← map_pow, ← pow_mod_orderOf, ← hmod]; simp)
  rw [← Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩, Nat.card_coe_set_eq,
    ncard_inversions_bipartiteCoxeterElement]

variable {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
include hnd hall

/-- **Steinberg's freeness of Coxeter orbits on roots** (Cartan-matrix form): when `b.cartanMatrix`
is of finite type with preconnected Dynkin diagram, for any Coxeter element `c = wordProd P b l`
and root index `j : ι`, the power `c ^ k` fixes `j` if and only if `orderOf c ∣ k`. -/
theorem weylGroupToPerm_wordProd_pow_apply_eq_self_iff_of_isFiniteType (j : ι) (k : ℕ) :
    P.weylGroupToPerm (wordProd P b l ^ k) j = j ↔ orderOf (wordProd P b l) ∣ k := by
  set c := wordProd P b l; classical
  refine ⟨fun hfix ↦ ?_, fun hdvd ↦ by
    rw [orderOf_dvd_iff_pow_eq_one.mp hdvd, map_one, Equiv.Perm.one_apply]⟩
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
  refine Nat.dvd_antisymm (Function.IsPeriodicPt.minimalPeriod_dvd (by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow, ← map_pow,
      pow_orderOf_eq_one, map_one, Equiv.Perm.one_apply])) ?_
  rw [← b.weylGroupToPerm_wordProd_pow_apply_eq_self_iff_of_isFiniteType hft hconn hnd hall j]
  simpa only [σ, Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow, ← map_pow] using
    Function.isPeriodicPt_minimalPeriod σ j

/-- Every `⟨wordProd P b l⟩`-orbit on the root indices has cardinality `orderOf (wordProd P b l)`
when `b.cartanMatrix` is of finite type with preconnected Dynkin diagram. -/
theorem ncard_setOf_sameCycle_weylGroupToPerm_wordProd_of_isFiniteType (j : ι) :
    {k : ι | Equiv.Perm.SameCycle (P.weylGroupToPerm (wordProd P b l)) j k}.ncard =
      orderOf (wordProd P b l) := by
  rw [Equiv.Perm.ncard_setOf_sameCycle,
    b.minimalPeriod_weylGroupToPerm_wordProd_of_isFiniteType hft hconn hnd hall j]

private theorem natCard_eq_card_quotient_mul_orderOf_wordProd :
    Nat.card ι = Nat.card (Quotient (Equiv.Perm.SameCycle.setoid
      (P.weylGroupToPerm (wordProd P b l)))) * orderOf (wordProd P b l) := by
  let := Fintype.ofFinite ι; classical
  have hsum := Equiv.Perm.sum_quotient_sameCycle_sum_range (P.weylGroupToPerm (wordProd P b l))
    fun _ ↦ (1 : ℕ)
  simp only [b.minimalPeriod_weylGroupToPerm_wordProd_of_isFiniteType hft hconn hnd hall,
    Finset.sum_const, Finset.card_range, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; exact hsum.symm

private theorem natCard_eq_card_support_mul_orderOf_wordProd_subsingleton [Subsingleton b.support] :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) := by
  let := Fintype.ofFinite ι
  by_cases hne : Nonempty b.support
  · obtain ⟨i₀⟩ := hne; set c := wordProd P b l with hc
    have hc_eq (a : b.support) : c = weylGroup.ofIdx P (a : ι) := by
      rw [hc, hnd.eq_singleton_of_mem (hall i₀), wordProd_cons, wordProd_nil, mul_one,
        Subsingleton.elim i₀ a]
    have hword_pow (lw : List b.support) : wordProd P b lw = c ^ lw.length := by
      induction lw with
      | nil => simp
      | cons a lw ih => rw [wordProd_cons, ih, ← hc_eq a, List.length_cons, pow_succ']
    have huniv : {k : ι | Equiv.Perm.SameCycle (P.weylGroupToPerm c) (i₀ : ι) k} = Set.univ :=
      Set.eq_univ_of_forall fun j ↦ by
        obtain ⟨i, hi, w, rfl⟩ := exists_mem_support_weylGroupToPerm_eq b j
        obtain ⟨lw, -, hw⟩ := (weylCoxeterSystem P b).exists_isReduced w
        rw [weylCoxeterSystem_wordProd, hword_pow] at hw
        have hi_eq : i = (i₀ : ι) := congrArg Subtype.val (Subsingleton.elim ⟨i, hi⟩ i₀)
        exact ⟨lw.length, by rw [zpow_natCast, ← map_pow, hw, hi_eq]⟩
    have hncard := b.ncard_setOf_sameCycle_weylGroupToPerm_wordProd_of_isFiniteType hft hconn
      hnd hall (i₀ : ι)
    rw [huniv, Set.ncard_univ] at hncard
    rw [← Fintype.card_coe, Fintype.card_eq_one_iff.mpr ⟨i₀, (Subsingleton.elim · i₀)⟩,
      one_mul, hncard]
  · rw [not_nonempty_iff] at hne
    have : IsEmpty ι := ⟨fun j ↦
      let ⟨i, hi, _, _⟩ := exists_mem_support_weylGroupToPerm_eq b j; hne.false ⟨i, hi⟩⟩
    simp [Nat.card_eq_fintype_card, ← Fintype.card_coe]

/-- **Bourbaki's root-count formula `|Φ| = r · h`** (Cartan-matrix form): when `b.cartanMatrix` is
of finite type with preconnected Dynkin diagram, the number of roots equals `b.support.card` times
the order of any Coxeter element `wordProd P b l` (requiring neither spanning nor irreducibility
over `R`). -/
theorem natCard_eq_card_support_mul_orderOf_wordProd_of_isFiniteType :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) := by
  classical
  by_cases hsub : Subsingleton b.support
  · exact b.natCard_eq_card_support_mul_orderOf_wordProd_subsingleton hft hconn hnd hall
  · have : Nontrivial b.support := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨col⟩ := nonempty_coloring_graph_coxeterMatrixOfBase_of_isFiniteType P b hft
    obtain ⟨_, _, -, -, hnd₀, hall₀, hword₀⟩ :=
      (weylCoxeterSystem P b).exists_wordProd_eq_bipartiteCoxeterElement col
    rw [weylCoxeterSystem_wordProd] at hword₀
    have hu := (weylCoxeterSystem P b).isConj_wordProd_bipartiteCoxeterElement
      (isAcyclic_graph_coxeterMatrixOfBase_of_isFiniteType P b hft) col hnd hall
    rw [weylCoxeterSystem_wordProd] at hu
    rw [b.natCard_eq_card_quotient_mul_orderOf_wordProd hft hconn hnd₀ hall₀, hword₀,
      b.card_quotient_sameCycle_bipartite_of_isFiniteType hft hconn col, hu.choose_spec.orderOf_eq]

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
      b.support.card := by
  have := P.finite_weylGroup_of_base b
  exact Nat.mul_right_cancel (orderOf_pos (wordProd P b l)) <|
    (b.natCard_eq_card_quotient_mul_orderOf_wordProd hft hconn hnd hall).symm.trans
      (b.natCard_eq_card_support_mul_orderOf_wordProd_of_isFiniteType hft hconn hnd hall)

/-- **Steinberg's unique inversion per Coxeter orbit** (Cartan-matrix form): when `b.cartanMatrix`
is of finite type with preconnected Dynkin diagram, for any Coxeter element `c = wordProd P b l`
and any root index `j : ι`, the `⟨c⟩`-orbit of `j` contains a unique root index in
`inversions P b c`. -/
theorem existsUnique_sameCycle_mem_inversions_wordProd_of_isFiniteType (j : ι) :
    ∃! k : ι, Equiv.Perm.SameCycle (P.weylGroupToPerm (wordProd P b l)) j k ∧
      k ∈ inversions P b (wordProd P b l) := by
  let c := wordProd P b l
  let f : inversions P b c → Quotient (Equiv.Perm.SameCycle.setoid (P.weylGroupToPerm c)) :=
    fun k ↦ Quotient.mk _ k.val
  have hbij : Function.Bijective f := (Nat.bijective_iff_surjective_and_card f).mpr
    ⟨b.surjective_quotientMk_inversions_wordProd hnd hall, by
      rw [Nat.card_coe_set_eq, ncard_inversions_wordProd_eq_card_support P b hnd hall,
        b.card_quotient_sameCycle_weylGroupToPerm_wordProd_of_isFiniteType hft hconn hnd hall]⟩
  obtain ⟨⟨k, hk_inv⟩, hk_eq⟩ := hbij.surjective ⟦j⟧
  refine ⟨k, ⟨(Quotient.exact hk_eq).symm, hk_inv⟩, fun y ⟨hy_sc, hy_inv⟩ ↦ ?_⟩
  have hy_eq : f ⟨y, hy_inv⟩ = f ⟨k, hk_inv⟩ := (Quotient.sound hy_sc.symm).trans hk_eq.symm
  exact congrArg Subtype.val (hbij.injective hy_eq)

/-- For any Coxeter element `c = wordProd P b l` (with `b.cartanMatrix` of finite type and
preconnected Dynkin diagram) and any root index `j : ι`, a unique `m : Fin (orderOf c)` sends `j`
under `P.weylGroupToPerm (c ^ (m : ℕ))` into `inversions P b c`. -/
theorem existsUnique_pow_mem_inversions_wordProd_of_isFiniteType (j : ι) :
    ∃! m : Fin (orderOf (wordProd P b l)),
      P.weylGroupToPerm (wordProd P b l ^ (m : ℕ)) j ∈ inversions P b (wordProd P b l) := by
  have := P.finite_weylGroup_of_base b; let c := wordProd P b l
  obtain ⟨k, ⟨hk_sc, hk_inv⟩, hk_uniq⟩ :=
    b.existsUnique_sameCycle_mem_inversions_wordProd_of_isFiniteType hft hconn hnd hall j
  obtain ⟨n, rfl⟩ := hk_sc.exists_nat_pow_eq
  let m₀ : Fin (orderOf c) := ⟨n % orderOf c, Nat.mod_lt n (orderOf_pos c)⟩
  have hm₀_eq : P.weylGroupToPerm (c ^ (m₀ : ℕ)) j = (P.weylGroupToPerm c ^ n) j := by
    dsimp only [m₀]; rw [pow_mod_orderOf, map_pow]
  refine ⟨m₀, by dsimp only; rwa [hm₀_eq], fun m hm ↦ ?_⟩
  have heq : P.weylGroupToPerm (c ^ (m : ℕ)) j = P.weylGroupToPerm (c ^ (m₀ : ℕ)) j :=
    (hk_uniq _ ⟨⟨(m : ℤ), by rw [zpow_natCast, map_pow]⟩, hm⟩).trans hm₀_eq.symm
  rw [map_pow, map_pow, Equiv.Perm.coe_pow, Equiv.Perm.coe_pow] at heq
  have hper := (b.minimalPeriod_weylGroupToPerm_wordProd_of_isFiniteType hft hconn hnd hall j).symm
  exact Fin.ext ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
    (lt_of_lt_of_eq m.isLt hper) (lt_of_lt_of_eq m₀.isLt hper)).mp heq)

end FiniteType

section Irreducible

variable [P.IsIrreducible] (b : P.Base) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
include hnd hall

/-- **Steinberg's freeness of Coxeter orbits on roots.** For any Coxeter element
`c = wordProd P b l` of an irreducible finite crystallographic reduced root pairing and any root
index `j : ι`, the power `c ^ k` fixes `j` if and only if `orderOf c ∣ k`. -/
theorem weylGroupToPerm_wordProd_pow_apply_eq_self_iff (j : ι) (k : ℕ) :
    P.weylGroupToPerm (wordProd P b l ^ k) j = j ↔ orderOf (wordProd P b l) ∣ k := by
  have : Nonempty ι := ⟨j⟩; have : NeZero (2 : R) := ⟨by norm_num⟩
  exact b.weylGroupToPerm_wordProd_pow_apply_eq_self_iff_of_isFiniteType
    (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall j k

/-- Every root index `j : ι` has minimal period `orderOf (wordProd P b l)` under a Coxeter element
`wordProd P b l`. -/
theorem minimalPeriod_weylGroupToPerm_wordProd (j : ι) :
    Function.minimalPeriod (P.weylGroupToPerm (wordProd P b l)) j = orderOf (wordProd P b l) := by
  have : Nonempty ι := ⟨j⟩; have : NeZero (2 : R) := ⟨by norm_num⟩
  exact b.minimalPeriod_weylGroupToPerm_wordProd_of_isFiniteType
    (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall j

/-- Every `⟨wordProd P b l⟩`-orbit of a root index has cardinality `orderOf (wordProd P b l)`. -/
theorem ncard_setOf_sameCycle_weylGroupToPerm_wordProd (j : ι) :
    {k : ι | Equiv.Perm.SameCycle (P.weylGroupToPerm (wordProd P b l)) j k}.ncard =
      orderOf (wordProd P b l) := by
  rw [Equiv.Perm.ncard_setOf_sameCycle, b.minimalPeriod_weylGroupToPerm_wordProd hnd hall j]

/-- **Bourbaki's root-count formula `|Φ| = r · h`.** In a finite, reduced, irreducible,
crystallographic root pairing with base `b`, the total number of roots equals the rank
`b.support.card` times the order of any Coxeter element `wordProd P b l`. -/
theorem natCard_eq_card_support_mul_orderOf_wordProd :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) := by
  let := Fintype.ofFinite ι
  by_cases hne : Nonempty ι
  · have : NeZero (2 : R) := ⟨by norm_num⟩
    exact b.natCard_eq_card_support_mul_orderOf_wordProd_of_isFiniteType
      (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall
  · have : IsEmpty ι := not_nonempty_iff.mp hne; have : IsEmpty b.support := ⟨(IsEmpty.false ·.val)⟩
    simp [Nat.card_eq_fintype_card, ← Fintype.card_coe]

/-- **Positive-root count formula `2 |Φ⁺| = r · h`.** Twice the number of positive roots equals
`b.support.card * orderOf (wordProd P b l)`. -/
theorem two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd :
    2 * (posRoots P b).ncard = b.support.card * orderOf (wordProd P b l) :=
  (two_mul_ncard_posRoots P b).trans (b.natCard_eq_card_support_mul_orderOf_wordProd hnd hall)

/-- **Positive-root count formula `|Φ⁺| = r · h / 2`.** -/
theorem ncard_posRoots_eq_card_support_mul_orderOf_wordProd_div_two :
    (posRoots P b).ncard = b.support.card * orderOf (wordProd P b l) / 2 := by
  rw [ncard_posRoots_eq_natCard_div_two, b.natCard_eq_card_support_mul_orderOf_wordProd hnd hall]

/-- **Number of Coxeter orbits on roots.** Every Coxeter element `wordProd P b l` partitions the
root indices `ι` into `b.support.card` cyclic orbits. -/
theorem card_quotient_sameCycle_weylGroupToPerm_wordProd :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (P.weylGroupToPerm (wordProd P b l)))) =
      b.support.card := by
  let := Fintype.ofFinite ι; classical
  by_cases hne : Nonempty ι
  · have : NeZero (2 : R) := ⟨by norm_num⟩
    exact b.card_quotient_sameCycle_weylGroupToPerm_wordProd_of_isFiniteType
      (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall
  · have : IsEmpty ι := not_nonempty_iff.mp hne; have : IsEmpty b.support := ⟨(IsEmpty.false ·.val)⟩
    have : IsEmpty (Quotient (Equiv.Perm.SameCycle.setoid (P.weylGroupToPerm (wordProd P b l)))) :=
      ⟨Quotient.ind IsEmpty.false⟩
    simp [Nat.card_eq_fintype_card, ← Fintype.card_coe]

/-- **Steinberg's unique inversion per Coxeter orbit.** For any Coxeter element
`c = wordProd P b l` and any root index `j : ι`, the `⟨c⟩`-orbit of `j` contains a unique root
index in `inversions P b c`. -/
theorem existsUnique_sameCycle_mem_inversions_wordProd (j : ι) :
    ∃! k : ι, Equiv.Perm.SameCycle (P.weylGroupToPerm (wordProd P b l)) j k ∧
      k ∈ inversions P b (wordProd P b l) := by
  have : Nonempty ι := ⟨j⟩; have : NeZero (2 : R) := ⟨by norm_num⟩
  exact b.existsUnique_sameCycle_mem_inversions_wordProd_of_isFiniteType
    (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall j

/-- For any Coxeter element `c = wordProd P b l` and any root index `j : ι`, a unique
`m : Fin (orderOf c)` sends `j` under `P.weylGroupToPerm (c ^ (m : ℕ))` into `inversions P b c`. -/
theorem existsUnique_pow_mem_inversions_wordProd (j : ι) :
    ∃! m : Fin (orderOf (wordProd P b l)),
      P.weylGroupToPerm (wordProd P b l ^ (m : ℕ)) j ∈ inversions P b (wordProd P b l) := by
  have : Nonempty ι := ⟨j⟩; have : NeZero (2 : R) := ⟨by norm_num⟩
  exact b.existsUnique_pow_mem_inversions_wordProd_of_isFiniteType
    (isFiniteType_cartanMatrix b) (preconnected_diagramGraph_cartanMatrix b) hnd hall j

end Irreducible

end Orbits

end RootPairing.Base

end
