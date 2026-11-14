/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Chart
public import TauCeti.Combinatorics.Young.LittlewoodRichardson.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# The bijection between fixed-boundary integer hives and Littlewood–Richardson tableaux

Fixed-boundary normalized integer hives with clockwise boundary
`productBoundary lam μ γ = (λ, μ, γ*)` are in explicit bijection with Littlewood–Richardson
tableaux. Using the product chart and determinant-shift equivalences from
`TauCeti.Combinatorics.Hive.Chart`, this file constructs that equivalence at the level of objects,
first for polynomial dominant weights (`TauCeti.Hive.fixedIntegerHiveEquivLRTableau`) and then, by
affine determinant shifts, for arbitrary signed dominant weights of `GL n`
(`TauCeti.Hive.fixedIntegerHiveEquivLRTableauOfShift`,
`TauCeti.Hive.fixedIntegerHiveDetShiftEquivLRTableau`, and
`TauCeti.Hive.hiveCount_productBoundary`).

For polynomial dominant weights `λ, μ, γ`, a Littlewood–Richardson tableau `T` of skew shape
`γ / λ` and content `μ` maps to the integer hive with chart values
`lrChart lam T i j = ∑_{r < j} λ_r + ∑_{l < i} ∑_{r < j} rowCount_T(r, l)`. Conversely, from a
fixed-boundary integer hive `h` one extracts the row-letter multiplicities `hiveRowCount h r l` as
the off-diagonal mixed second forward difference for `l < r < n` and the diagonal step
`h(l + 1, l + 1) - h(l, l + 1)` for `l = r < n`. Elementary-cell concavity gives nonnegativity off
the diagonal, vertical-strip concavity propagates nonnegativity from the `μ`-boundary onto the
diagonal, horizontal-strip concavity gives column strictness of the reconstructed skew tableau, and
vertical-strip concavity gives the Yamanouchi lattice-word condition.

## Main definitions

* `TauCeti.Hive.lrChart`: chart values associated to a Littlewood–Richardson tableau.
* `TauCeti.Hive.hiveOfLRTableau`: fixed-boundary integer hive constructed from an `LRTableau`.
* `TauCeti.Hive.hiveRowCountInt`, `TauCeti.Hive.hiveRowCount`: row-letter multiplicities extracted
  from an integer hive.
* `TauCeti.Hive.lrTableauOfHive`: `LRTableau` reconstructed from a fixed-boundary integer hive.
* `TauCeti.Hive.fixedIntegerHiveEquivLRTableau`: explicit equivalence
  `FixedIntegerHive (productBoundary lam μ γ) ≃ LRTableau lam.shape γ.shape μ.shape` for polynomial
  dominant weights.
* `TauCeti.Hive.fixedIntegerHiveEquivLRTableauOfShift`,
  `TauCeti.Hive.fixedIntegerHiveDetShiftEquivLRTableau`: determinant-shifted equivalences for
  general signed dominant weights.

## Main results

* `TauCeti.Hive.hiveCount_productBoundary_eq_natCard_lrTableau`,
  `TauCeti.Hive.hiveCount_productBoundary_of_isPolynomial`,
  `TauCeti.Hive.hiveCount_productBoundary_eq_ite_shift`,
  `TauCeti.Hive.hiveCount_productBoundary`: Littlewood–Richardson tableau count formulas for
  polynomial and arbitrary signed dominant weights, together with shift independence.
* `TauCeti.Hive.hiveCount_productBoundary_zero_left`,
  `TauCeti.Hive.hiveCount_productBoundary_zero_right`: unit-weight hive counts.
* `TauCeti.Hive.hiveCount_one_productBoundary`, `TauCeti.Hive.hiveCount_two_std_dual_triv`,
  `TauCeti.Hive.hiveCount_three_checks`: rank-`1`, signed rank-`2`, and rank-`3` checks.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Appendix 2.
* A. S. Buch, *The saturation conjecture (after A. Knutson and T. Tao)*, Enseign. Math. (2) **46**
  (2000), 43–60, Appendix A.
* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), §5.2.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

section Bijection

variable {n : ℕ}

/-! ### Forward map: from a Littlewood–Richardson tableau to an integer hive -/

/-- Chart values of the integer hive associated to a Littlewood–Richardson tableau `T`:
`lrChart lam T i j = ∑_{r < j} λ_r + ∑_{l < i} ∑_{r < j} rowCount_T(r, l)`. -/
def lrChart (lam : DominantWeight n) {γ μ : YoungDiagram}
    (T : LRTableau lam.shape γ μ) (i j : ℕ) : ℤ :=
  (∑ r : Fin n with r.val < j, lam.1 r) +
    ∑ l ∈ Finset.range i, ∑ r ∈ Finset.range j, (T.1.rowCount r l : ℤ)

/-- Along `i = 0`, `lrChart lam T 0 j` is the partial sum of the first `j` entries of `lam`. -/
@[simp] theorem lrChart_zero_left (lam : DominantWeight n) {γ μ : YoungDiagram}
    (T : LRTableau lam.shape γ μ) (j : ℕ) :
    lrChart lam T 0 j = ∑ r : Fin n with r.val < j, lam.1 r := by
  simp [lrChart]

/-- Along `j = 0`, `lrChart lam T i 0` vanishes. -/
@[simp] theorem lrChart_zero_right (lam : DominantWeight n) {γ μ : YoungDiagram}
    (T : LRTableau lam.shape γ μ) (i : ℕ) :
    lrChart lam T i 0 = 0 := by
  simp [lrChart]

private theorem sum_fin_lt_eq_sum_range (f : Fin n → ℤ) (g : ℕ → ℤ) {k : ℕ} (hk : k ≤ n)
    (hfg : ∀ r (hr : r < n), f ⟨r, hr⟩ = g r) :
    (∑ r : Fin n with r.val < k, f r) = ∑ r ∈ Finset.range k, g r := by
  rw [show ({r : Fin n | r.val < k} : Finset (Fin n)) =
      Finset.univ.map (Fin.castLEEmb hk) by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    exact ⟨fun hr => ⟨⟨r.val, hr⟩, Fin.ext rfl⟩, fun ⟨s, hs⟩ => hs ▸ s.isLt⟩,
    Finset.sum_map, ← Fin.sum_univ_eq_sum_range g k]
  exact Finset.sum_congr rfl fun r _ => hfg r.val (r.isLt.trans_le hk)

private theorem lrChart_right {lam μ γ : DominantWeight n} (hμ : μ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) (i : ℕ) (hi : i ≤ n) :
    lrChart lam T i n = (∑ r : Fin n, lam.1 r) + ∑ l : Fin n with l.val < i, μ.1 l := by
  rw [lrChart, show ({r : Fin n | r.val < n} : Finset (Fin n)) = Finset.univ by ext r; simp]
  congr 1
  rw [sum_fin_lt_eq_sum_range μ.1 (fun l => (μ.shape.rowLen l : ℤ)) hi
    (fun l hl => (μ.natCast_rowLen_shape hμ ⟨l, hl⟩).symm)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Nat.cast_sum, T.1.sum_range_rowCount_eq_content l γ.colLen_zero_shape_le,
    congrFun T.2.1 l]

private theorem lrChart_diag {lam μ γ : DominantWeight n} (hlam : lam.IsPolynomial)
    (hγ : γ.IsPolynomial) (T : LRTableau lam.shape γ.shape μ.shape) (j : ℕ) (hj : j ≤ n) :
    lrChart lam T j j = ∑ r : Fin n with r.val < j, γ.1 r := by
  rw [lrChart,
    sum_fin_lt_eq_sum_range lam.1 (fun r => (lam.shape.rowLen r : ℤ)) hj
      (fun r hr => (lam.natCast_rowLen_shape hlam ⟨r, hr⟩).symm),
    sum_fin_lt_eq_sum_range γ.1 (fun r => (γ.shape.rowLen r : ℤ)) hj
      (fun r hr => (γ.natCast_rowLen_shape hγ ⟨r, hr⟩).symm),
    Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrj : r < j := Finset.mem_range.mp hr
  have hrow : ∑ l ∈ Finset.range j, T.1.rowCount r l =
      γ.shape.rowLen r - lam.shape.rowLen r :=
    T.1.sum_range_rowCount_of_forall_lt fun c _ _ => (T.entry_le r c).trans_lt hrj
  have hle : lam.shape.rowLen r ≤ γ.shape.rowLen r := YoungDiagram.rowLen_le_of_le T.1.le r
  rw [← Nat.cast_sum, hrow]
  omega

private theorem lrChart_step_right (lam : DominantWeight n) {γ μ : YoungDiagram}
    (T : LRTableau lam.shape γ μ) (i j : ℕ) (hj : j < n) :
    lrChart lam T i (j + 1) - lrChart lam T i j =
      lam.1 ⟨j, hj⟩ + ∑ l ∈ Finset.range i, (T.1.rowCount j l : ℤ) := by
  have hsplit : ({r : Fin n | r.val < j + 1} : Finset (Fin n)) =
      insert ⟨j, hj⟩ ({r : Fin n | r.val < j} : Finset (Fin n)) := by
    ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]; omega
  have hnm : (⟨j, hj⟩ : Fin n) ∉ ({r : Fin n | r.val < j} : Finset (Fin n)) := by simp
  simp only [lrChart, hsplit, Finset.sum_insert hnm, Finset.sum_range_succ, Finset.sum_add_distrib]
  abel

private theorem isRhombusConcave_lrChart {lam μ γ : DominantWeight n} (hlam : lam.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) :
    IsRhombusConcave (fun p : Vertex n => lrChart lam T p.z (n - p.x)) := by
  rw [isRhombusConcave_iff_ofChart]
  have hval (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
      (let p := Vertex.ofChart n i j hij hjn; lrChart lam T p.z (n - p.x)) = lrChart lam T i j := by
    simp only [Vertex.ofChart_z, Vertex.ofChart_x, Nat.sub_sub_self hjn]
  refine ⟨fun i j hij hjn => ?_, fun i j hij hjn => ?_, fun i j hij hjn => ?_⟩
  · simp only [hval]
    have h0 := lrChart_step_right lam T i j (by omega)
    have h1 := lrChart_step_right lam T (i + 1) (j + 1) (by omega)
    have hcol : (lam.shape.rowLen (j + 1) : ℤ) +
        (∑ l ∈ Finset.range (i + 1), (T.1.rowCount (j + 1) l : ℤ)) ≤
        (lam.shape.rowLen j : ℤ) + ∑ l ∈ Finset.range i, (T.1.rowCount j l : ℤ) := by
      exact_mod_cast T.1.rowLen_add_sum_range_rowCount_succ_le j i
    rw [lam.natCast_rowLen_shape hlam ⟨j + 1, by omega⟩,
      lam.natCast_rowLen_shape hlam ⟨j, by omega⟩] at hcol
    linarith
  · simp only [hval]
    have h0 : lrChart lam T (i + 1) j - lrChart lam T i j =
        ∑ r ∈ Finset.range j, (T.1.rowCount r i : ℤ) := by simp [lrChart, Finset.sum_range_succ]
    have h1 : lrChart lam T (i + 1) (j + 1) - lrChart lam T i (j + 1) =
        (∑ r ∈ Finset.range j, (T.1.rowCount r i : ℤ)) + (T.1.rowCount j i : ℤ) := by
      simp [lrChart, Finset.sum_range_succ]
    linarith [Int.natCast_nonneg (T.1.rowCount j i)]
  · simp only [hval]
    have h0 : lrChart lam T (i + 1) j - lrChart lam T i j =
        ∑ r ∈ Finset.range j, (T.1.rowCount r i : ℤ) := by simp [lrChart, Finset.sum_range_succ]
    have h1 : lrChart lam T (i + 2) (j + 1) - lrChart lam T (i + 1) (j + 1) =
        ∑ r ∈ Finset.range (j + 1), (T.1.rowCount r (i + 1) : ℤ) := by
      simp [lrChart, Finset.sum_range_succ]
    have hlat : (∑ r ∈ Finset.range (j + 1), (T.1.rowCount r (i + 1) : ℤ)) ≤
        ∑ r ∈ Finset.range j, (T.1.rowCount r i : ℤ) := by
      exact_mod_cast (T.1.isLatticeWord_readingWord_iff.mp T.2.2) i j
    linarith

private def hiveOfLRTableauAux {lam μ γ : DominantWeight n} (hlam : lam.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) : IntegerHive n where
  value p := lrChart lam T p.z (n - p.x)
  value_cornerA' := by simp
  le_of_isRhombus' hr := (isRhombusConcave_def _).mp (isRhombusConcave_lrChart hlam T) hr

@[simp] private theorem hiveOfLRTableauAux_apply {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (T : LRTableau lam.shape γ.shape μ.shape) (p : Vertex n) :
    hiveOfLRTableauAux hlam T p = lrChart lam T p.z (n - p.x) :=
  rfl

/-- Normalized integer hive constructed from a Littlewood–Richardson tableau `T` for polynomial
dominant weights `lam, μ, γ`. -/
def hiveOfLRTableau {lam μ γ : DominantWeight n} (hlam : lam.IsPolynomial)
    (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) : FixedIntegerHive (productBoundary lam μ γ) :=
  ⟨hiveOfLRTableauAux hlam T, by
    ext s k
    have hk := k.isLt
    rcases (by fin_cases s <;> decide : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl
    · simp only [boundary_apply, hiveOfLRTableauAux_apply, Vertex.edgePoint_zero_z,
        Vertex.edgePoint_zero_x, Fin.val_succ, Fin.val_castSucc,
        Nat.sub_sub_self (by omega : k.val + 1 ≤ n), Nat.sub_sub_self (by omega : k.val ≤ n),
        lrChart_zero_left, productBoundary_zero]
      have hsplit : ({r : Fin n | r.val < k.val + 1} : Finset (Fin n)) =
          insert k ({r : Fin n | r.val < k.val} : Finset (Fin n)) := by
        ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff]; omega
      rw [hsplit, Finset.sum_insert (by simp)]; abel
    · simp only [boundary_apply, hiveOfLRTableauAux_apply, Vertex.edgePoint_one_z,
        Vertex.edgePoint_one_x, Nat.sub_zero, Fin.val_succ, Fin.val_castSucc,
        productBoundary_one]
      rw [lrChart_right hμ T (k.val + 1) (by omega), lrChart_right hμ T k.val (by omega)]
      have hsplit : ({l : Fin n | l.val < k.val + 1} : Finset (Fin n)) =
          insert k ({l : Fin n | l.val < k.val} : Finset (Fin n)) := by
        ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff]; omega
      rw [hsplit, Finset.sum_insert (by simp)]; abel
    · simp only [boundary_apply, hiveOfLRTableauAux_apply, Vertex.edgePoint_two_z,
        Vertex.edgePoint_two_x, Fin.val_succ, Fin.val_castSucc,
        productBoundary_two, DominantWeight.dual_apply]
      rw [lrChart_diag hlam hγ T (n - (k.val + 1)) (by omega),
        lrChart_diag hlam hγ T (n - k.val) (by omega)]
      have hsplit : ({r : Fin n | r.val < n - k.val} : Finset (Fin n)) =
          insert k.rev ({r : Fin n | r.val < n - (k.val + 1)} : Finset (Fin n)) := by
        ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff, Fin.val_rev]; omega
      have hnm : k.rev ∉ ({r : Fin n | r.val < n - (k.val + 1)} : Finset (Fin n)) := by
        simp [Fin.val_rev]
      rw [hsplit, Finset.sum_insert hnm]; abel⟩

/-- Evaluating `hiveOfLRTableau` at `Vertex.ofChart n i j` recovers `lrChart lam T i j`. -/
@[simp] theorem hiveOfLRTableau_apply_ofChart {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    (hiveOfLRTableau hlam hμ hγ T).1 (Vertex.ofChart n i j hij hjn) = lrChart lam T i j := by
  simp [hiveOfLRTableau, Nat.sub_sub_self hjn]

/-! ### Inverse map: extracting row-letter multiplicities from an integer hive -/

/-- Integer row-letter multiplicity extracted from a hive `h`: off-diagonal mixed second difference
for `l < r < n`, diagonal step `h(l + 1, l + 1) - h(l, l + 1)` for `l = r < n`, and `0` elsewhere.
-/
def hiveRowCountInt (h : IntegerHive n) (r l : ℕ) : ℤ :=
  if hlr : l < r ∧ r < n then
    h (Vertex.ofChart n (l + 1) (r + 1) (by omega) (by omega)) -
      h (Vertex.ofChart n l (r + 1) (by omega) (by omega)) -
      h (Vertex.ofChart n (l + 1) r hlr.1 hlr.2.le) +
      h (Vertex.ofChart n l r hlr.1.le hlr.2.le)
  else if heq : l = r ∧ r < n then
    h (Vertex.ofChart n (l + 1) (l + 1) le_rfl (by omega)) -
      h (Vertex.ofChart n l (l + 1) (by omega) (by omega))
  else 0

/-- Natural-number row-letter multiplicity extracted from an integer hive. -/
def hiveRowCount (h : IntegerHive n) (r l : ℕ) : ℕ :=
  (hiveRowCountInt h r l).toNat

/-- Off the diagonal (`l < r < n`), `hiveRowCountInt h r l` is the mixed second difference of `h`
across cell `(l, r)`. -/
theorem hiveRowCountInt_of_lt (h : IntegerHive n) {r l : ℕ} (hlr : l < r) (hrn : r < n) :
    hiveRowCountInt h r l =
      h (Vertex.ofChart n (l + 1) (r + 1) (by omega) (by omega)) -
        h (Vertex.ofChart n l (r + 1) (by omega) (by omega)) -
        h (Vertex.ofChart n (l + 1) r hlr hrn.le) +
        h (Vertex.ofChart n l r hlr.le hrn.le) := by
  unfold hiveRowCountInt
  split_ifs with h₁
  · rfl
  · exact absurd ⟨hlr, hrn⟩ h₁
  · exact absurd ⟨hlr, hrn⟩ h₁

/-- On the diagonal (`l < n`), `hiveRowCountInt h l l` is `h(l + 1, l + 1) - h(l, l + 1)`. -/
theorem hiveRowCountInt_diag (h : IntegerHive n) {l : ℕ} (hln : l < n) :
    hiveRowCountInt h l l =
      h (Vertex.ofChart n (l + 1) (l + 1) le_rfl (by omega)) -
        h (Vertex.ofChart n l (l + 1) (by omega) (by omega)) := by
  unfold hiveRowCountInt
  split_ifs with h₁ h₂
  · omega
  · rfl
  · exact absurd ⟨rfl, hln⟩ h₂

/-- Above the diagonal (`r < l`), `hiveRowCountInt h r l` vanishes. -/
theorem hiveRowCountInt_eq_zero_of_lt (h : IntegerHive n) {r l : ℕ} (hrl : r < l) :
    hiveRowCountInt h r l = 0 := by
  unfold hiveRowCountInt
  split_ifs <;> omega

/-- Beyond row `n` (`n ≤ r`), `hiveRowCountInt h r l` vanishes. -/
theorem hiveRowCountInt_eq_zero_of_le (h : IntegerHive n) {r : ℕ} (hr : n ≤ r) (l : ℕ) :
    hiveRowCountInt h r l = 0 := by
  unfold hiveRowCountInt
  split_ifs <;> omega

/-- Above the diagonal (`r < l`), `hiveRowCount h r l` vanishes. -/
@[simp] theorem hiveRowCount_eq_zero_of_lt (h : IntegerHive n) {r l : ℕ} (hrl : r < l) :
    hiveRowCount h r l = 0 := by
  simp [hiveRowCount, hiveRowCountInt_eq_zero_of_lt h hrl]

/-- Beyond row `n` (`n ≤ r`), `hiveRowCount h r l` vanishes. -/
@[simp] theorem hiveRowCount_eq_zero_of_le (h : IntegerHive n) {r : ℕ} (hr : n ≤ r) (l : ℕ) :
    hiveRowCount h r l = 0 := by
  simp [hiveRowCount, hiveRowCountInt_eq_zero_of_le h hr l]

/-- Summing `hiveRowCountInt h r l` over rows `r < j` (with `l < j ≤ n`) telescopes to the
vertical chart difference `h(l + 1, j) - h(l, j)`. -/
theorem sum_range_hiveRowCountInt_left (h : IntegerHive n) {l j : ℕ} (hlj : l < j)
    (hjn : j ≤ n) :
    ∑ r ∈ Finset.range j, hiveRowCountInt h r l =
      h (Vertex.ofChart n (l + 1) j hlj hjn) - h (Vertex.ofChart n l j hlj.le hjn) := by
  induction j with
  | zero => omega
  | succ m ih =>
    rw [Finset.sum_range_succ]
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hlj) with rfl | hlm
    · rw [Finset.sum_eq_zero fun r hr =>
        hiveRowCountInt_eq_zero_of_lt h (Finset.mem_range.mp hr),
        zero_add, hiveRowCountInt_diag h hjn]
    · rw [ih hlm (by omega), hiveRowCountInt_of_lt h hlm hjn]
      abel

/-- Double-sum reconstruction of `h(i, j) - h(0, j)` from `hiveRowCountInt`. -/
theorem sum_hiveRowCountInt_eq_sub (h : IntegerHive n) {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    (∑ l ∈ Finset.range i, ∑ r ∈ Finset.range j, hiveRowCountInt h r l) =
      h (Vertex.ofChart n i j hij hjn) - h (Vertex.ofChart n 0 j (Nat.zero_le j) hjn) := by
  induction i with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega),
      sum_range_hiveRowCountInt_left h (by omega) hjn]
    abel

/-- Partial row sum of `hiveRowCountInt` for `x ≤ r` and `r < n`. -/
private theorem sum_range_hiveRowCountInt_right_le (h : IntegerHive n) {r x : ℕ}
    (hxr : x ≤ r) (hrn : r < n) :
    ∑ l ∈ Finset.range x, hiveRowCountInt h r l =
      (h (Vertex.ofChart n x (r + 1) (by omega) hrn) - h (Vertex.ofChart n x r hxr hrn.le)) -
        (h (Vertex.ofChart n 0 (r + 1) (Nat.zero_le _) hrn) -
          h (Vertex.ofChart n 0 r (Nat.zero_le _) hrn.le)) := by
  induction x with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega), hiveRowCountInt_of_lt h (by omega) hrn]
    abel

/-- Full row sum of `hiveRowCountInt` for `r < n` and `r + 1 ≤ x`. -/
private theorem sum_range_hiveRowCountInt_right_ge (h : IntegerHive n) {r x : ℕ}
    (hrx : r + 1 ≤ x) (hrn : r < n) :
    ∑ l ∈ Finset.range x, hiveRowCountInt h r l =
      (h (Vertex.ofChart n (r + 1) (r + 1) le_rfl hrn) - h (Vertex.ofChart n r r le_rfl hrn.le)) -
        (h (Vertex.ofChart n 0 (r + 1) (Nat.zero_le _) hrn) -
          h (Vertex.ofChart n 0 r (Nat.zero_le _) hrn.le)) := by
  induction x with
  | zero => omega
  | succ m ih =>
    rw [Finset.sum_range_succ]
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hrx) with rfl | hrm
    · rw [sum_range_hiveRowCountInt_right_le h le_rfl hrn, hiveRowCountInt_diag h hrn]
      abel
    · rw [ih hrm, hiveRowCountInt_eq_zero_of_lt h hrm, add_zero]

private theorem diag_step_ge_of_productBoundary {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) :
    ∀ d l (hd : l + 1 + d = n),
      μ.1 ⟨n - 1, by omega⟩ ≤
        h (Vertex.ofChart n (l + 1) (l + 1) le_rfl (by omega)) -
          h (Vertex.ofChart n l (l + 1) (by omega) (by omega))
  | 0, l, hd => by
    have hln : l + 1 = n := by omega
    have he1 := apply_ofChart_right hb (l + 1) (by omega)
    have he0 := apply_ofChart_right hb l (by omega)
    have hch1 : Vertex.ofChart n (l + 1) (l + 1) le_rfl (by omega) =
        Vertex.ofChart n (l + 1) n (by omega) le_rfl := Vertex.ofChart_eq_iff.mpr ⟨rfl, hln⟩
    have hch0 : Vertex.ofChart n l (l + 1) (by omega) (by omega) =
        Vertex.ofChart n l n (by omega) le_rfl := Vertex.ofChart_eq_iff.mpr ⟨rfl, hln⟩
    have hsplit : ({k : Fin n | k.val < l + 1} : Finset (Fin n)) =
        insert ⟨l, by omega⟩ ({k : Fin n | k.val < l} : Finset (Fin n)) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff]; omega
    rw [congrArg h hch1, congrArg h hch0, he1, he0, hsplit, Finset.sum_insert (by simp)]
    have heql : (⟨n - 1, by omega⟩ : Fin n) = ⟨l, by omega⟩ := Fin.ext (by simp; omega)
    rw [heql]
    linarith
  | d + 1, l, hd => by
    have hv := h.le_of_isRhombus
      (isRhombus_ofChart_vert (n := n) (i := l) (j := l + 1) (by omega) (by omega))
    have hnext := diag_step_ge_of_productBoundary hb d (l + 1) (by omega)
    linarith

/-- Every `hiveRowCountInt h r l` is nonnegative when `h` has boundary `(λ, μ, γ*)` with
polynomial `μ`. -/
theorem hiveRowCountInt_nonneg {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hμ : μ.IsPolynomial) (r l : ℕ) :
    0 ≤ hiveRowCountInt h r l := by
  unfold hiveRowCountInt
  split_ifs with hlr heq
  · have hcell := h.le_of_isRhombus (isRhombus_ofChart_cell hlr.1 hlr.2)
    linarith
  · obtain ⟨rfl, hln⟩ := heq
    exact ((DominantWeight.isPolynomial_def μ).mp hμ ⟨n - 1, by omega⟩).trans
      (diag_step_ge_of_productBoundary hb (n - 1 - l) l (by omega))
  · exact le_rfl

private theorem natCast_hiveRowCount {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hμ : μ.IsPolynomial) (r l : ℕ) :
    (hiveRowCount h r l : ℤ) = hiveRowCountInt h r l :=
  Int.toNat_of_nonneg (hiveRowCountInt_nonneg hb hμ r l)

private theorem shape_le_of_productBoundary {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) :
    lam.shape ≤ γ.shape := by
  have hγ := isPolynomial_of_productBoundary hb hlam hμ
  refine YoungDiagram.le_of_forall_rowLen_le fun r => ?_
  by_cases hr : r < n
  · have hsum := sum_range_hiveRowCountInt_right_ge h le_rfl hr
    have hd1 := apply_ofChart_diag hb (r + 1) hr
    have hd0 := apply_ofChart_diag hb r hr.le
    have hl1 := apply_ofChart_zero_left hb (r + 1) hr
    have hl0 := apply_ofChart_zero_left hb r hr.le
    have hsplit : ({k : Fin n | k.val < r + 1} : Finset (Fin n)) =
        insert ⟨r, hr⟩ ({k : Fin n | k.val < r} : Finset (Fin n)) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff]; omega
    rw [hd1, hd0, hl1, hl0, hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
      at hsum
    have hnn : 0 ≤ ∑ l ∈ Finset.range (r + 1), hiveRowCountInt h r l :=
      Finset.sum_nonneg fun l _ => hiveRowCountInt_nonneg hb hμ r l
    have hle : lam.1 ⟨r, hr⟩ ≤ γ.1 ⟨r, hr⟩ := by linarith
    rw [← lam.natCast_rowLen_shape hlam ⟨r, hr⟩, ← γ.natCast_rowLen_shape hγ ⟨r, hr⟩] at hle
    exact Int.ofNat_le.mp hle
  · simp [lam.rowLen_shape_eq_zero_of_le (not_lt.mp hr)]

private theorem sum_hiveRowCount_eq_rowLen_sub {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (r : ℕ) :
    ∑ l ∈ Finset.range n, hiveRowCount h r l = γ.shape.rowLen r - lam.shape.rowLen r := by
  have hγ := isPolynomial_of_productBoundary hb hlam hμ
  by_cases hr : r < n
  · have hle : lam.shape.rowLen r ≤ γ.shape.rowLen r :=
      YoungDiagram.rowLen_le_of_le (shape_le_of_productBoundary hb hlam hμ) r
    refine Int.ofNat_inj.mp ?_
    rw [Nat.cast_sum, Nat.cast_sub hle,
      Finset.sum_congr rfl fun l _ => natCast_hiveRowCount hb hμ r l,
      sum_range_hiveRowCountInt_right_ge h hr hr,
      apply_ofChart_diag hb (r + 1) hr, apply_ofChart_diag hb r hr.le,
      apply_ofChart_zero_left hb (r + 1) hr, apply_ofChart_zero_left hb r hr.le,
      γ.natCast_rowLen_shape hγ ⟨r, hr⟩, lam.natCast_rowLen_shape hlam ⟨r, hr⟩]
    have hsplit : ({k : Fin n | k.val < r + 1} : Finset (Fin n)) =
        insert ⟨r, hr⟩ ({k : Fin n | k.val < r} : Finset (Fin n)) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff]; omega
    rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    abel
  · rw [γ.rowLen_shape_eq_zero_of_le (not_lt.mp hr), lam.rowLen_shape_eq_zero_of_le (not_lt.mp hr)]
    simp [hiveRowCount_eq_zero_of_le h (not_lt.mp hr)]

private theorem col_strict_hiveRowCount {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (r x : ℕ) :
    lam.shape.rowLen (r + 1) + ∑ l ∈ Finset.range (x + 1), hiveRowCount h (r + 1) l ≤
      lam.shape.rowLen r + ∑ l ∈ Finset.range x, hiveRowCount h r l := by
  by_cases hr1 : r + 2 ≤ n
  · refine Int.ofNat_le.mp ?_
    push_cast
    simp only [natCast_hiveRowCount hb hμ]
    rw [lam.natCast_rowLen_shape hlam ⟨r + 1, by omega⟩,
      lam.natCast_rowLen_shape hlam ⟨r, by omega⟩]
    have hsplit (m : ℕ) (hm : m < n) : ({k : Fin n | k.val < m + 1} : Finset (Fin n)) =
        insert ⟨m, hm⟩ ({k : Fin n | k.val < m} : Finset (Fin n)) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff]; omega
    rcases le_or_gt x r with hxr | hrx
    · have hs0 := sum_range_hiveRowCountInt_right_le h hxr (by omega)
      have hs1 := sum_range_hiveRowCountInt_right_le h (Nat.add_le_add_right hxr 1) (by omega)
      rw [apply_ofChart_zero_left hb (r + 1) (by omega), apply_ofChart_zero_left hb r (by omega),
        hsplit r (by omega), Finset.sum_insert (by simp)] at hs0
      rw [apply_ofChart_zero_left hb (r + 2) hr1, apply_ofChart_zero_left hb (r + 1) (by omega),
        hsplit (r + 1) (by omega), Finset.sum_insert (by simp)] at hs1
      have hrh := h.le_of_isRhombus (isRhombus_ofChart_horiz hxr hr1)
      linarith
    · have hs0 := sum_range_hiveRowCountInt_right_ge h hrx (by omega)
      have hs1 := sum_range_hiveRowCountInt_right_ge h (by omega : r + 2 ≤ x + 1) (by omega)
      rw [apply_ofChart_diag hb (r + 1) (by omega), apply_ofChart_diag hb r (by omega),
        apply_ofChart_zero_left hb (r + 1) (by omega), apply_ofChart_zero_left hb r (by omega),
        hsplit r (by omega), Finset.sum_insert (by simp), Finset.sum_insert (by simp)] at hs0
      rw [apply_ofChart_diag hb (r + 2) hr1, apply_ofChart_diag hb (r + 1) (by omega),
        apply_ofChart_zero_left hb (r + 2) hr1, apply_ofChart_zero_left hb (r + 1) (by omega),
        hsplit (r + 1) (by omega), Finset.sum_insert (by simp), Finset.sum_insert (by simp)] at hs1
      have hanti : γ.1 ⟨r + 1, by omega⟩ ≤ γ.1 ⟨r, by omega⟩ :=
        γ.antitone (Fin.mk_le_mk.mpr (Nat.le_succ r))
      linarith
  · have hrn : n ≤ r + 1 := by omega
    rw [lam.rowLen_shape_eq_zero_of_le hrn,
      Finset.sum_eq_zero fun l _ => hiveRowCount_eq_zero_of_le h hrn l]
    omega

private theorem lattice_hiveRowCount {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hμ : μ.IsPolynomial) (k x : ℕ) :
    ∑ r ∈ Finset.range (x + 1), hiveRowCount h r (k + 1) ≤
      ∑ r ∈ Finset.range x, hiveRowCount h r k := by
  rcases le_or_gt x k with hxk | hkx
  · rw [Finset.sum_eq_zero fun r hr =>
      hiveRowCount_eq_zero_of_lt h (by have := Finset.mem_range.mp hr; omega)]
    exact Nat.zero_le _
  · refine Int.ofNat_le.mp ?_
    push_cast
    simp only [natCast_hiveRowCount hb hμ]
    rcases lt_or_ge x n with hxn | hnx
    · rw [sum_range_hiveRowCountInt_left h (Nat.add_lt_add_right hkx 1) hxn,
        sum_range_hiveRowCountInt_left h hkx hxn.le]
      have hv := h.le_of_isRhombus (isRhombus_ofChart_vert hkx hxn)
      linarith
    · by_cases hk1 : k + 1 < n
      · have htrunc (m y : ℕ) (hny : n ≤ y) :
            ∑ r ∈ Finset.range y, hiveRowCountInt h r m =
              ∑ r ∈ Finset.range n, hiveRowCountInt h r m :=
          (Finset.sum_subset (Finset.range_mono hny) fun r _ hnr =>
            hiveRowCountInt_eq_zero_of_le h (not_lt.mp (mt Finset.mem_range.mpr hnr)) m).symm
        rw [htrunc (k + 1) (x + 1) (Nat.le_succ_of_le hnx), htrunc k x hnx,
          sum_range_hiveRowCountInt_left h hk1 le_rfl,
          sum_range_hiveRowCountInt_left h (by omega : k < n) le_rfl,
          apply_ofChart_right hb (k + 2) hk1, apply_ofChart_right hb (k + 1) hk1.le,
          apply_ofChart_right hb k (by omega)]
        have hsplit (m : ℕ) (hm : m < n) : ({l : Fin n | l.val < m + 1} : Finset (Fin n)) =
            insert ⟨m, hm⟩ ({l : Fin n | l.val < m} : Finset (Fin n)) := by
          ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Fin.ext_iff]; omega
        rw [hsplit (k + 1) hk1, Finset.sum_insert (by simp),
          hsplit k (by omega), Finset.sum_insert (by simp)]
        have hanti : μ.1 ⟨k + 1, hk1⟩ ≤ μ.1 ⟨k, by omega⟩ :=
          μ.antitone (Fin.mk_le_mk.mpr (Nat.le_succ k))
        linarith
      · rw [Finset.sum_eq_zero fun r _ => ?_]
        · exact Finset.sum_nonneg fun r _ => hiveRowCountInt_nonneg hb hμ r k
        · rcases lt_or_ge r n with hrn | hrn
          · exact hiveRowCountInt_eq_zero_of_lt h (by omega)
          · exact hiveRowCountInt_eq_zero_of_le h hrn (k + 1)

/-- Littlewood–Richardson tableau reconstructed from a fixed-boundary integer hive for polynomial
dominant weights `lam, μ`. -/
def lrTableauOfHive {lam μ γ : DominantWeight n} (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    LRTableau lam.shape γ.shape μ.shape := by
  have hle := shape_le_of_productBoundary h.2 hlam hμ
  have hsum := sum_hiveRowCount_eq_rowLen_sub h.2 hlam hμ
  have hcol := col_strict_hiveRowCount h.2 hlam hμ
  have hzero : ∀ r l, n ≤ l → hiveRowCount h.1 r l = 0 := fun r l hl => by
    rcases lt_or_ge r n with hr | hr
    · exact hiveRowCount_eq_zero_of_lt h.1 (hr.trans_le hl)
    · exact hiveRowCount_eq_zero_of_le h.1 hr l
  let S := SkewSemistandardYoungTableau.ofRowCount hle n (hiveRowCount h.1) hsum hcol
  refine ⟨S, funext fun k => ?_, S.isLatticeWord_readingWord_iff.mpr fun k x => ?_⟩
  · rw [← S.sum_range_rowCount_eq_content k γ.colLen_zero_shape_le]
    simp only [S, SkewSemistandardYoungTableau.rowCount_ofRowCount hle hsum hcol hzero]
    by_cases hk : k < n
    · refine Int.ofNat_inj.mp ?_
      rw [Nat.cast_sum, Finset.sum_congr rfl fun r _ => natCast_hiveRowCount h.2 hμ r k,
        sum_range_hiveRowCountInt_left h.1 hk le_rfl,
        apply_ofChart_right h.2 (k + 1) hk, apply_ofChart_right h.2 k hk.le,
        μ.natCast_rowLen_shape hμ ⟨k, hk⟩]
      have hsplit : ({l : Fin n | l.val < k + 1} : Finset (Fin n)) =
          insert ⟨k, hk⟩ ({l : Fin n | l.val < k} : Finset (Fin n)) := by
        ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff]; omega
      rw [hsplit, Finset.sum_insert (by simp)]
      abel
    · rw [μ.rowLen_shape_eq_zero_of_le (not_lt.mp hk)]
      exact Finset.sum_eq_zero fun r _ => hzero r k (not_lt.mp hk)
  · simp only [S, SkewSemistandardYoungTableau.rowCount_ofRowCount hle hsum hcol hzero]
    exact lattice_hiveRowCount h.2 hμ k x

/-- The row-letter multiplicity of `lrTableauOfHive` at `(r, l)` is `hiveRowCount h.1 r l`. -/
@[simp] theorem rowCount_lrTableauOfHive {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r l : ℕ) :
    (lrTableauOfHive hlam hμ h).1.rowCount r l = hiveRowCount h.1 r l := by
  refine SkewSemistandardYoungTableau.rowCount_ofRowCount _ _ _ (fun i k hk => ?_) r l
  rcases lt_or_ge i n with hi | hi
  · exact hiveRowCount_eq_zero_of_lt h.1 (hi.trans_le hk)
  · exact hiveRowCount_eq_zero_of_le h.1 hi k

/-- **Explicit equivalence between fixed-boundary integer hives and Littlewood–Richardson tableaux**
for polynomial dominant weights `lam, μ, γ` of `GL n`.

The hypothesis `hγ : γ.IsPolynomial` is necessary because `DominantWeight.shape` truncates negative
entries to `0`: at `n = 2`, `λ = (1, 0)`, `μ = (0, 0)`, `γ = (1, -1)` has no hive while
`LRTableau (1) (1) ⊥` has one element. -/
def fixedIntegerHiveEquivLRTableau {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial) :
    FixedIntegerHive (productBoundary lam μ γ) ≃ LRTableau lam.shape γ.shape μ.shape where
  toFun := lrTableauOfHive hlam hμ
  invFun := hiveOfLRTableau hlam hμ hγ
  left_inv h := Subtype.ext <| ext fun p => by
    have hp := p.sum_eq
    rw [← Vertex.ofChart_z_sub_x p, hiveOfLRTableau_apply_ofChart]
    simp only [lrChart, rowCount_lrTableauOfHive, natCast_hiveRowCount h.2 hμ]
    rw [sum_hiveRowCountInt_eq_sub h.1 (by omega) (Nat.sub_le n p.x),
      apply_ofChart_zero_left h.2 (n - p.x) (Nat.sub_le n p.x)]
    abel
  right_inv T := Subtype.ext <| SkewSemistandardYoungTableau.eq_of_rowCount_eq fun r l => by
    rw [rowCount_lrTableauOfHive]
    refine Int.ofNat_inj.mp ?_
    rw [natCast_hiveRowCount (hiveOfLRTableau hlam hμ hγ T).2 hμ]
    have hzero_lt : ∀ i k, i < k → T.1.rowCount i k = 0 := fun i k hik => by
      rw [SkewSemistandardYoungTableau.rowCount_def, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      intro c _ hc; have := T.entry_le i c; omega
    unfold hiveRowCountInt
    split_ifs with hlr heq
    · simp only [hiveOfLRTableau_apply_ofChart, lrChart, Finset.sum_range_succ]
      abel
    · obtain ⟨rfl, hln⟩ := heq
      simp only [hiveOfLRTableau_apply_ofChart, lrChart, Finset.sum_range_succ]
      have hsum0 : ∑ i ∈ Finset.range l, (T.1.rowCount i l : ℤ) = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [hzero_lt i l (Finset.mem_range.mp hi), Nat.cast_zero]
      rw [hsum0]
      abel
    · rcases lt_or_ge r l with hrl | hlr'
      · rw [hzero_lt r l hrl, Nat.cast_zero]
      · have hrn : n ≤ r := by omega
        rw [T.1.rowCount_eq_zero_of_colLen_le (γ.colLen_zero_shape_le.trans hrn) l, Nat.cast_zero]

/-- Forward action of `fixedIntegerHiveEquivLRTableau` on row-letter multiplicities. -/
@[simp] theorem rowCount_fixedIntegerHiveEquivLRTableau {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r l : ℕ) :
    (fixedIntegerHiveEquivLRTableau hlam hμ hγ h).1.rowCount r l = hiveRowCount h.1 r l :=
  rowCount_lrTableauOfHive hlam hμ h r l

/-- Inverse action of `fixedIntegerHiveEquivLRTableau` in `Vertex.ofChart` coordinates. -/
@[simp] theorem fixedIntegerHiveEquivLRTableau_symm_apply_ofChart {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    ((fixedIntegerHiveEquivLRTableau hlam hμ hγ).symm T).1 (Vertex.ofChart n i j hij hjn) =
      lrChart lam T i j :=
  hiveOfLRTableau_apply_ofChart hlam hμ hγ T i j hij hjn

/-- For polynomial dominant weights `lam, μ, γ`, `hiveCount (productBoundary lam μ γ)` equals the
Littlewood–Richardson coefficient `Nat.card (LRTableau lam.shape γ.shape μ.shape)`. -/
theorem hiveCount_productBoundary_eq_natCard_lrTableau {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial) :
    hiveCount (productBoundary lam μ γ) = Nat.card (LRTableau lam.shape γ.shape μ.shape) := by
  rw [← natCard_fixedIntegerHive]
  exact Nat.card_congr (fixedIntegerHiveEquivLRTableau hlam hμ hγ)

open scoped Classical in
/-- For polynomial input weights `lam, μ` and any dominant weight `γ`, `hiveCount` equals the
Littlewood–Richardson coefficient when `γ` is polynomial and `0` otherwise. -/
theorem hiveCount_productBoundary_of_isPolynomial {lam μ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (γ : DominantWeight n) :
    hiveCount (productBoundary lam μ γ) =
      if γ.IsPolynomial then Nat.card (LRTableau lam.shape γ.shape μ.shape) else 0 := by
  split_ifs with hγ
  · exact hiveCount_productBoundary_eq_natCard_lrTableau hlam hμ hγ
  · exact hiveCount_eq_zero_iff.mpr ⟨fun ⟨h, hb⟩ => hγ (isPolynomial_of_productBoundary hb hlam hμ)⟩

/-! ### Signed dominant weights and determinant-shift independence -/

/-- Object equivalence between `FixedIntegerHive (productBoundary lam μ γ)` and
Littlewood–Richardson tableaux for arbitrary signed dominant weights shifted into the polynomial
cone by `(a, b)`. -/
def fixedIntegerHiveEquivLRTableauOfShift {lam μ γ : DominantWeight n} {a b : ℤ}
    (hla : (lam.shift a).IsPolynomial) (hmb : (μ.shift b).IsPolynomial)
    (hgc : (γ.shift (a + b)).IsPolynomial) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      LRTableau (lam.shift a).shape (γ.shift (a + b)).shape (μ.shift b).shape :=
  (fixedIntegerHiveShiftEquiv lam μ γ a b).trans (fixedIntegerHiveEquivLRTableau hla hmb hgc)

/-- Canonical determinant-shifted equivalence between `FixedIntegerHive (productBoundary lam μ γ)`
and Littlewood–Richardson tableaux of shapes `lam.detShiftShape` and `μ.detShiftShape`, whenever
`lam.detShift + μ.detShift ≤ γ.detShift`. -/
def fixedIntegerHiveDetShiftEquivLRTableau {lam μ γ : DominantWeight n}
    (hdet : lam.detShift + μ.detShift ≤ γ.detShift) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      LRTableau lam.detShiftShape
        (γ.shift (-(lam.detShift + μ.detShift))).shape μ.detShiftShape := by
  have hneg : -lam.detShift + -μ.detShift = -(lam.detShift + μ.detShift) := by omega
  have hgc : (γ.shift (-lam.detShift + -μ.detShift)).IsPolynomial := by
    rw [hneg, DominantWeight.isPolynomial_iff_zero_le_detShift]
    match n, lam, μ, γ, hdet with
    | 0, _, _, _, _ => simp
    | _ + 1, _, _, _, hdet => rw [DominantWeight.detShift_shift]; omega
  have hsh (w : DominantWeight n) : (w.shift (-w.detShift)).shape = w.detShiftShape := by
    rw [← w.weightOfShape_detShiftShape, shape_weightOfShape w.colLen_zero_detShiftShape_le]
  rw [← hsh lam, ← hsh μ, ← hneg]
  exact fixedIntegerHiveEquivLRTableauOfShift lam.isPolynomial_shift_neg_detShift
    μ.isPolynomial_shift_neg_detShift hgc

open scoped Classical in
/-- **Shift independence of Littlewood–Richardson hive counts**: for any shifts `a, b : ℤ` making
`lam.shift a` and `μ.shift b` polynomial, the shifted tableau count equals
`hiveCount (productBoundary lam μ γ)` and hence does not depend on `(a, b)`. -/
theorem hiveCount_productBoundary_eq_ite_shift {lam μ : DominantWeight n} (γ : DominantWeight n)
    {a b : ℤ} (hla : (lam.shift a).IsPolynomial) (hmb : (μ.shift b).IsPolynomial) :
    hiveCount (productBoundary lam μ γ) =
      if (γ.shift (a + b)).IsPolynomial then
        Nat.card (LRTableau (lam.shift a).shape (γ.shift (a + b)).shape (μ.shift b).shape)
      else 0 := by
  rw [← hiveCount_productBoundary_shift lam μ γ a b,
    hiveCount_productBoundary_of_isPolynomial hla hmb]

/-- **Littlewood–Richardson formula for `hiveCount` on arbitrary signed dominant weights** via the
canonical determinant-twist decomposition. -/
theorem hiveCount_productBoundary (lam μ γ : DominantWeight n) :
    hiveCount (productBoundary lam μ γ) =
      if lam.detShift + μ.detShift ≤ γ.detShift then
        Nat.card (LRTableau lam.detShiftShape
          (γ.shift (-(lam.detShift + μ.detShift))).shape μ.detShiftShape)
      else 0 := by
  split_ifs with hdet
  · rw [← natCard_fixedIntegerHive]
    exact Nat.card_congr (fixedIntegerHiveDetShiftEquivLRTableau hdet)
  · exact hiveCount_eq_zero_iff.mpr ⟨fun ⟨h, hb⟩ => hdet (detShift_le_of_productBoundary hb)⟩

/-! ### Unit-weight fibres and concrete checks -/

private theorem isPolynomial_zero : (0 : DominantWeight n).IsPolynomial :=
  (DominantWeight.isPolynomial_def 0).mpr (by simp)

private theorem shape_zero : (0 : DominantWeight n).shape = ⊥ :=
  YoungDiagram.rowLen_injective <| funext fun i => by
    by_cases hi : i < n
    · simpa using (0 : DominantWeight n).rowLen_shape ⟨i, hi⟩
    · simpa using (0 : DominantWeight n).rowLen_shape_eq_zero_of_le (not_lt.mp hi)

open scoped Classical in
/-- With trivial first input weight `0`, `productBoundary 0 μ γ` has one integer hive when `γ = μ`
and none otherwise. -/
theorem hiveCount_productBoundary_zero_left (μ γ : DominantWeight n) :
    hiveCount (productBoundary 0 μ γ) = if γ = μ then 1 else 0 := by
  rw [← hiveCount_productBoundary_shift_right 0 μ γ (-μ.detShift),
    hiveCount_productBoundary_of_isPolynomial isPolynomial_zero μ.isPolynomial_shift_neg_detShift,
    shape_zero, natCard_lrTableau_bot_left]
  rcases eq_or_ne γ μ with rfl | h
  · simp [γ.isPolynomial_shift_neg_detShift]
  · simp only [h, ↓reduceIte]
    split_ifs with hp hm
    · exfalso
      apply h
      have heq : γ.shift (-μ.detShift) = μ.shift (-μ.detShift) := by
        rw [← weightOfShape_shape hp, ← weightOfShape_shape μ.isPolynomial_shift_neg_detShift, hm]
      calc γ = (γ.shift (-μ.detShift)).shift μ.detShift := by simp
        _ = (μ.shift (-μ.detShift)).shift μ.detShift := by rw [heq]
        _ = μ := by simp
    · rfl
    · rfl

open scoped Classical in
/-- With trivial second input weight `0`, `productBoundary lam 0 γ` has one integer hive when
`γ = lam` and none otherwise. -/
theorem hiveCount_productBoundary_zero_right (lam γ : DominantWeight n) :
    hiveCount (productBoundary lam 0 γ) = if γ = lam then 1 else 0 := by
  rw [← hiveCount_productBoundary_shift_left lam 0 γ (-lam.detShift),
    hiveCount_productBoundary_of_isPolynomial lam.isPolynomial_shift_neg_detShift isPolynomial_zero,
    shape_zero, natCard_lrTableau_bot_right]
  rcases eq_or_ne γ lam with rfl | h
  · simp [γ.isPolynomial_shift_neg_detShift]
  · simp only [h, ↓reduceIte]
    split_ifs with hp hl
    · exfalso
      apply h
      have heq : γ.shift (-lam.detShift) = lam.shift (-lam.detShift) := by
        rw [← weightOfShape_shape hp, ← weightOfShape_shape lam.isPolynomial_shift_neg_detShift, hl]
      calc γ = (γ.shift (-lam.detShift)).shift lam.detShift := by simp
        _ = (lam.shift (-lam.detShift)).shift lam.detShift := by rw [heq]
        _ = lam := by simp
    · rfl
    · rfl

/-- Rank-`1` hive check: `hiveCount (productBoundary a b g) = 1` if `g = a + b` and `0` otherwise.
-/
theorem hiveCount_one_productBoundary (a b g : DominantWeight 1) :
    hiveCount (productBoundary a b g) = if g = a + b then 1 else 0 := by
  have ha : a = (0 : DominantWeight 1).shift (a.1 0) := by ext i; fin_cases i; simp
  have hb : b = (0 : DominantWeight 1).shift (b.1 0) := by ext i; fin_cases i; simp
  have hg : g = (g.shift (-(a.1 0 + b.1 0))).shift (a.1 0 + b.1 0) := by simp
  conv_lhs => rw [ha, hb, hg, hiveCount_productBoundary_shift, hiveCount_productBoundary_zero_left]
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
  · ext i; fin_cases i
    have h0 := congrArg (fun w : DominantWeight 1 => w.1 0) h
    simp only [DominantWeight.shift_apply, DominantWeight.zero_apply, DominantWeight.add_apply]
      at h0 ⊢
    change g.1 0 = a.1 0 + b.1 0
    omega
  · subst h; ext i; fin_cases i; simp

/-- Signed rank-`2` check: `λ = (1, 0), μ = (0, -1), γ = (0, 0)` has `hiveCount = 1`
(the trivial invariant in `V ⊗ V*`), whereas truncating negative entries to `0` would give
`((1, 0), (0, 0), (0, 0))` with `hiveCount = 0`. -/
theorem hiveCount_two_std_dual_triv :
    hiveCount (productBoundary ⟨![1, 0], by decide⟩ ⟨![0, -1], by decide⟩ ⟨![0, 0], by decide⟩) = 1
      ∧ hiveCount
        (productBoundary ⟨![1, 0], by decide⟩ ⟨![0, 0], by decide⟩ ⟨![0, 0], by decide⟩) = 0 := by
  let lam : DominantWeight 2 := ⟨![1, 0], by decide⟩
  let μ : DominantWeight 2 := ⟨![0, -1], by decide⟩
  let γ : DominantWeight 2 := ⟨![0, 0], by decide⟩
  constructor
  · have hsh : productBoundary (lam.shift 0) (μ.shift 1) (γ.shift (0 + 1)) =
        productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![1, 1], by decide⟩ := by
      ext s i
      fin_cases s <;> fin_cases i <;>
        simp [productBoundary_zero, productBoundary_one, productBoundary_two, lam, μ, γ]
    rw [← hiveCount_productBoundary_shift lam μ γ 0 1, hsh]
    exact hiveCount_two_std_std_det
  · refine hiveCount_eq_zero_of_sum_ne_zero ?_
    simp [Fin.sum_univ_three, Fin.sum_univ_two,
      productBoundary_zero, productBoundary_one, productBoundary_two]

private theorem isRhombusConcave_of_chartThree (c : ℕ → ℕ → ℤ)
    (hH : c 0 0 + c 1 2 ≤ c 0 1 + c 1 1 ∧ c 0 1 + c 1 3 ≤ c 0 2 + c 1 2 ∧
      c 1 1 + c 2 3 ≤ c 1 2 + c 2 2)
    (hC : c 1 1 + c 0 2 ≤ c 0 1 + c 1 2 ∧ c 1 2 + c 0 3 ≤ c 0 2 + c 1 3 ∧
      c 2 2 + c 1 3 ≤ c 1 2 + c 2 3)
    (hV : c 0 1 + c 2 2 ≤ c 1 1 + c 1 2 ∧ c 0 2 + c 2 3 ≤ c 1 2 + c 1 3 ∧
      c 1 2 + c 3 3 ≤ c 2 2 + c 2 3) :
    IsRhombusConcave (fun p : Vertex 3 => c p.z (3 - p.x)) := by
  rw [isRhombusConcave_iff_ofChart]
  have hv (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ 3) :
      (let p := Vertex.ofChart 3 i j hij hjn; c p.z (3 - p.x)) = c i j := by
    simp only [Vertex.ofChart_z, Vertex.ofChart_x, Nat.sub_sub_self hjn]
  refine ⟨fun i j hij hjn => ?_, fun i j hij hjn => ?_, fun i j hij hjn => ?_⟩
  · simp only [hv]
    rcases (by omega : (i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 1)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hH.1
    · exact hH.2.1
    · exact hH.2.2
  · simp only [hv]
    rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hC.1
    · exact hC.2.1
    · exact hC.2.2
  · simp only [hv]
    rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hV.1
    · exact hV.2.1
    · exact hV.2.2

/-- A rank-`3` hive with fixed boundary `B` is uniquely determined by its value at the single
interior vertex `(1, 1, 1)`. -/
private theorem fixedIntegerHive_three_ext {B : Fin 3 → Fin 3 → ℤ}
    (k₁ k₂ : FixedIntegerHive B)
    (hmid : k₁.1 ⟨1, 1, 1, rfl⟩ = k₂.1 ⟨1, 1, 1, rfl⟩) : k₁ = k₂ := by
  refine Subtype.ext <| ext fun p => ?_
  have := p.sum_eq
  by_cases hz : p.z = 0
  · have he : p = Vertex.edgePoint 3 0 ⟨p.y, by omega⟩ := by ext <;> simp [hz]; omega
    rw [he, k₁.1.apply_edgePoint_zero, k₂.1.apply_edgePoint_zero, k₁.2, k₂.2]
  · by_cases hx : p.x = 0
    · have he : p = Vertex.edgePoint 3 1 ⟨p.z, by omega⟩ := by ext <;> simp [hx]; omega
      rw [he, k₁.1.apply_edgePoint_one, k₂.1.apply_edgePoint_one, k₁.2, k₂.2]
    · by_cases hy : p.y = 0
      · have he : p = Vertex.edgePoint 3 2 ⟨p.x, by omega⟩ := by ext <;> simp [hy]; omega
        rw [he, k₁.1.apply_edgePoint_two, k₂.1.apply_edgePoint_two, k₁.2, k₂.2]
      · have hm : p = ⟨1, 1, 1, rfl⟩ := by ext <;> simp <;> omega
        rw [hm, hmid]

/-- Rhombus bounds on the interior value `k.1 (1, 1, 1)` of any rank-`3` product-boundary hive. -/
private theorem apply_center_bounds_three {lam μ γ : DominantWeight 3}
    (k : FixedIntegerHive (productBoundary lam μ γ)) :
    lam.1 0 + lam.1 2 + μ.1 0 ≤ k.1 ⟨1, 1, 1, rfl⟩ ∧
      k.1 ⟨1, 1, 1, rfl⟩ ≤ lam.1 0 + lam.1 1 + μ.1 0 := by
  have hch12 : Vertex.ofChart 3 1 2 (by decide) (by decide) = ⟨1, 1, 1, rfl⟩ := by ext <;> simp
  have hsumlt (w : DominantWeight 3) (j : ℕ) :
      (∑ r : Fin 3 with r.val < j, w.1 r) =
        (if 0 < j then w.1 0 else 0) + (if 1 < j then w.1 1 else 0) +
          (if 2 < j then w.1 2 else 0) := by
    simp [Finset.sum_filter, Fin.sum_univ_three, add_assoc]
  have hrH := k.1.le_of_isRhombus
    (isRhombus_ofChart_horiz (n := 3) (i := 0) (j := 1) (by decide) (by decide))
  have hrC := k.1.le_of_isRhombus
    (isRhombus_ofChart_cell (n := 3) (i := 0) (j := 2) (by decide) (by decide))
  rw [apply_ofChart_zero_left k.2, apply_ofChart_zero_left k.2, apply_ofChart_right k.2,
    Fin.sum_univ_three, hsumlt, hsumlt, hsumlt, congrArg k.1 hch12] at hrH
  rw [apply_ofChart_zero_left k.2, apply_ofChart_zero_left k.2, apply_ofChart_right k.2,
    Fin.sum_univ_three, hsumlt, hsumlt, hsumlt, congrArg k.1 hch12] at hrC
  simp only [Nat.lt_add_one, Nat.zero_lt_two, Nat.one_lt_ofNat, lt_self_iff_false,
    Nat.not_ofNat_lt_one, ↓reduceIte] at hrH hrC
  omega

/-- Rank-`3` check `c^{(2, 0, 0)}_{(1, 0, 0), (1, 0, 0)} = 1` and the classic multiplicity-two
example `c^{(3, 2, 1)}_{(2, 1, 0), (2, 1, 0)} = 2`, whose unique interior vertex `(1, 1, 1)` takes
the two values `4` and `5`. -/
theorem hiveCount_three_checks :
    hiveCount
      (productBoundary ⟨![1, 0, 0], by decide⟩ ⟨![1, 0, 0], by decide⟩ ⟨![2, 0, 0], by decide⟩) = 1
    ∧ hiveCount
      (productBoundary ⟨![2, 1, 0], by decide⟩ ⟨![2, 1, 0], by decide⟩ ⟨![3, 2, 1], by decide⟩) = 2
    := by
  let B₁ := productBoundary (⟨![1, 0, 0], by decide⟩ : DominantWeight 3)
    ⟨![1, 0, 0], by decide⟩ ⟨![2, 0, 0], by decide⟩
  let B₂ := productBoundary (⟨![2, 1, 0], by decide⟩ : DominantWeight 3)
    ⟨![2, 1, 0], by decide⟩ ⟨![3, 2, 1], by decide⟩
  let c₁ (i j : ℕ) : ℤ := if j = 0 then 0 else if i = 0 then 1 else 2
  let c₂ (m : ℤ) (i j : ℕ) : ℤ :=
    if i = 0 then (if j = 0 then 0 else if j = 1 then 2 else 3)
    else if i = 1 then (if j = 1 then 3 else if j = 2 then m else 5)
    else if j = 2 then 5 else 6
  let h₁ : FixedIntegerHive B₁ :=
    ⟨⟨fun p => c₁ p.z (3 - p.x), by simp [c₁],
        fun hr => (isRhombusConcave_def _).mp
          (isRhombusConcave_of_chartThree c₁ (by decide) (by decide) (by decide)) hr⟩,
      by ext s k; fin_cases s <;> fin_cases k <;>
        simp [B₁, c₁, boundary_apply, productBoundary_zero, productBoundary_one,
          productBoundary_two]⟩
  let mk₂ (m : ℤ) (hm : m = 4 ∨ m = 5) : FixedIntegerHive B₂ :=
    ⟨⟨fun p => c₂ m p.z (3 - p.x), by simp [c₂],
        fun hr => (isRhombusConcave_def _).mp (isRhombusConcave_of_chartThree (c₂ m)
          (by rcases hm with rfl | rfl <;> decide)
          (by rcases hm with rfl | rfl <;> decide)
          (by rcases hm with rfl | rfl <;> decide)) hr⟩,
      by ext s k; fin_cases s <;> fin_cases k <;>
        simp [B₂, c₂, boundary_apply, productBoundary_zero, productBoundary_one,
          productBoundary_two]⟩
  let h₂₄ := mk₂ 4 (Or.inl rfl)
  let h₂₅ := mk₂ 5 (Or.inr rfl)
  constructor
  · rw [← card_fixedIntegerHive]
    refine Fintype.card_eq_one_iff.mpr ⟨h₁, fun k => fixedIntegerHive_three_ext k h₁ ?_⟩
    have hb := apply_center_bounds_three k
    change (1 : ℤ) + 0 + 1 ≤ k.1 ⟨1, 1, 1, rfl⟩ ∧ k.1 ⟨1, 1, 1, rfl⟩ ≤ 1 + 0 + 1 at hb
    exact le_antisymm hb.2 hb.1
  · have huniv : (Finset.univ : Finset (FixedIntegerHive B₂)) = {h₂₄, h₂₅} := by
      ext k
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      have hb := apply_center_bounds_three k
      change (2 : ℤ) + 0 + 2 ≤ k.1 ⟨1, 1, 1, rfl⟩ ∧ k.1 ⟨1, 1, 1, rfl⟩ ≤ 2 + 1 + 2 at hb
      rcases (by omega : k.1 ⟨1, 1, 1, rfl⟩ = 4 ∨ k.1 ⟨1, 1, 1, rfl⟩ = 5) with h4 | h5
      · exact Or.inl (fixedIntegerHive_three_ext k h₂₄ h4)
      · exact Or.inr (fixedIntegerHive_three_ext k h₂₅ h5)
    have hne : h₂₄ ≠ h₂₅ := fun h => by
      have hm : (4 : ℤ) = 5 := congrArg (fun k : FixedIntegerHive B₂ => k.1 ⟨1, 1, 1, rfl⟩) h
      omega
    rw [← card_fixedIntegerHive, ← Finset.card_univ, huniv, Finset.card_pair hne]

end Bijection

end TauCeti.Hive
