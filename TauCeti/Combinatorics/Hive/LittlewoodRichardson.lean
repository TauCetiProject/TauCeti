/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Fibre
public import TauCeti.Combinatorics.Young.LittlewoodRichardson.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# The hive–Littlewood–Richardson equivalence

In the `(i, j)` product chart `Vertex.ofChart n i j = (n - j, j - i, i)` (`0 ≤ i ≤ j ≤ n`), the
three-family rhombus characterization (`TauCeti.Hive.isRhombusConcave_iff_ofChart` in
`TauCeti.Combinatorics.Hive.Basic`) expresses rhombus concavity by three families of inequalities:
right-leaning, left-leaning, and upright unit rhombi.

For polynomial dominant weights `λ, μ, γ` of `GLₙ`, these three families match the defining
conditions of a Littlewood–Richardson tableau `T : LRTableau λ.shape γ.shape μ.shape` under the
partial-sum dictionary
$$
  H(i, j) = \sum_{r < j} \lambda_r + \sum_{k < i} \sum_{r < j} m_{r, k},
$$
where `m_{r, k} = T.1.rowCount r k` is the multiplicity of the letter `k` in row `r` of `T`:

* right-leaning rhombi encode column strictness of the skew tableau `T`;
* left-leaning rhombi encode the lattice-word (ballot) condition on the reading word of `T`;
* upright rhombi encode nonnegativity `0 ≤ m_{r, k}` off the diagonal, while diagonal nonnegativity
  `0 ≤ m_{k, k}` follows inductively from left-leaning rhombi anchored on `μ_{n - 1} ≥ 0`.

This yields an explicit bijection `TauCeti.Hive.fixedIntegerHiveEquivLRTableau` between
`FixedIntegerHive (productBoundary λ μ γ)` and `LRTableau λ.shape γ.shape μ.shape`. For arbitrary
signed dominant weights, adding the normalized affine hive `affine n a (a + b)`
(`TauCeti.Hive.shiftProductBoundaryEquiv`) reduces any product-boundary fibre to polynomial
weights, giving shift-independent bijections (`fixedIntegerHiveEquivLRTableauShift`,
`fixedIntegerHiveEquivLRTableauDetShift`), the shift-transport `lrTableauShiftEquiv` comparing
different admissible shift pairs, and the unconditional count
`hiveCount_productBoundary_eq_ite_natCard_lrTableau`.

For the downstream applications of this equivalence to Schur polynomials and `GLₙ(ℂ)` rational
Weyl-module tensor multiplicities, see `TauCeti.Combinatorics.Hive.Schur` and
`TauCeti.Combinatorics.Hive.TensorProduct`.

## Main definitions

* `TauCeti.Hive.hiveOfLRTableau`, `TauCeti.Hive.lrTableauOfHive`: the two directions of the
  hive–Littlewood–Richardson dictionary on polynomial dominant weights.
* `TauCeti.Hive.fixedIntegerHiveEquivLRTableau`: explicit bijection between polynomial-boundary
  integer hives and Littlewood–Richardson tableaux.
* `TauCeti.Hive.fixedIntegerHiveEquivLRTableauShift`,
  `TauCeti.Hive.fixedIntegerHiveEquivLRTableauDetShift`: signed-weight bijections via affine
  determinant shifts.
* `TauCeti.Hive.lrTableauShiftEquiv`: canonical transport between shifted
  Littlewood–Richardson tableaux for different admissible shift pairs.

## Main results

* `TauCeti.Hive.rowCount_lrTableauOfHive_of_lt`, `TauCeti.Hive.rowCount_lrTableauOfHive_diag`:
  pointwise row-count formulas for `lrTableauOfHive`.
* `TauCeti.Hive.hiveOfLRTableau_lrTableauOfHive`, `TauCeti.Hive.lrTableauOfHive_hiveOfLRTableau`:
  round-trip identities for the standalone maps.
* `TauCeti.Hive.eq_lrTableauShiftEquiv_iff`: characterization of `lrTableauShiftEquiv` by
  unchanged off-diagonal row counts and diagonal counts shifted by `b₂ - b₁`.
* `TauCeti.Hive.hiveCount_productBoundary_eq_natCard_lrTableau`,
  `TauCeti.Hive.hiveCount_productBoundary_eq_ite_natCard_lrTableau`: hive counts equal
  Littlewood–Richardson coefficients for polynomial and arbitrary signed weights.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Appendix 2.
* A. S. Buch, *The saturation conjecture (after A. Knutson and T. Tao)*, Enseign. Math. (2) **46**
  (2000), 43–60, §2 and Appendix.
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §2, Theorem 1.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

/-! ### Forward map: Littlewood–Richardson tableaux to integer hives -/

section ForwardMap

variable {n : ℕ} {lam μ γ : DominantWeight n}

/-- Partial-sum lattice function associated to a Littlewood–Richardson tableau `T`. -/
private def lrHiveFun (T : LRTableau lam.shape γ.shape μ.shape) (p : Vertex n) : ℤ :=
  (∑ r ∈ Finset.range (p.y + p.z), (lam.shape.rowLen r : ℤ)) +
    ∑ k ∈ Finset.range p.z, ∑ r ∈ Finset.range (p.y + p.z), (T.val.rowCount r k : ℤ)

private theorem lrHiveFun_ofChart (T : LRTableau lam.shape γ.shape μ.shape) {i j : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) :
    lrHiveFun T (Vertex.ofChart n i j hij hjn) =
      (∑ r ∈ Finset.range j, (lam.shape.rowLen r : ℤ)) +
        ∑ k ∈ Finset.range i, ∑ r ∈ Finset.range j, (T.val.rowCount r k : ℤ) := by
  simp [lrHiveFun, Nat.sub_add_cancel hij]

private theorem lrHiveFun_step_j (T : LRTableau lam.shape γ.shape μ.shape) {i j : ℕ}
    (hij : i ≤ j) (hjn : j + 1 ≤ n) :
    lrHiveFun T (Vertex.ofChart n i (j + 1) (by omega) hjn) -
        lrHiveFun T (Vertex.ofChart n i j hij (by omega)) =
      (lam.shape.rowLen j : ℤ) + ∑ k ∈ Finset.range i, (T.val.rowCount j k : ℤ) := by
  rw [lrHiveFun_ofChart, lrHiveFun_ofChart, Finset.sum_range_succ]
  simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
  abel

private theorem lrHiveFun_step_i (T : LRTableau lam.shape γ.shape μ.shape) {i j : ℕ}
    (hij : i < j) (hjn : j ≤ n) :
    lrHiveFun T (Vertex.ofChart n (i + 1) j hij hjn) -
        lrHiveFun T (Vertex.ofChart n i j hij.le hjn) =
      ∑ r ∈ Finset.range j, (T.val.rowCount r i : ℤ) := by
  rw [lrHiveFun_ofChart, lrHiveFun_ofChart, Finset.sum_range_succ]
  abel

private theorem isRhombusConcave_lrHiveFun (T : LRTableau lam.shape γ.shape μ.shape) :
    IsRhombusConcave (lrHiveFun T) := by
  rw [isRhombusConcave_iff_ofChart]
  refine ⟨fun i j hij hjn => ?_, fun i j hij hjn => ?_, fun i j hij hjn => ?_⟩
  · have h1 := lrHiveFun_step_i T (i := i) (j := j + 1) (by omega) hjn
    have h2 := lrHiveFun_step_i T (i := i) (j := j) hij hjn.le
    rw [Finset.sum_range_succ] at h1
    linarith [Int.natCast_nonneg (T.val.rowCount j i)]
  · have h1 := lrHiveFun_step_i T (i := i + 1) (j := j + 1) (by omega) hjn
    have h2 := lrHiveFun_step_i T (i := i) (j := j) hij hjn.le
    have hlat : ∑ r ∈ Finset.range (j + 1), (T.val.rowCount r (i + 1) : ℤ) ≤
        ∑ r ∈ Finset.range j, (T.val.rowCount r i : ℤ) := by
      exact_mod_cast (T.val.isLatticeWord_readingWord_iff.mp T.property.2) i j
    linarith
  · have h1 := lrHiveFun_step_j T (i := i + 1) (j := j + 1) (by omega) hjn
    have h2 := lrHiveFun_step_j T (i := i) (j := j) hij (by omega)
    have hcol : (lam.shape.rowLen (j + 1) : ℤ) +
        ∑ k ∈ Finset.range (i + 1), (T.val.rowCount (j + 1) k : ℤ) ≤
        (lam.shape.rowLen j : ℤ) + ∑ k ∈ Finset.range i, (T.val.rowCount j k : ℤ) := by
      exact_mod_cast T.val.rowLen_add_sum_range_rowCount_succ_le j i
    linarith

private theorem lrHiveFun_step_diag (T : LRTableau lam.shape γ.shape μ.shape) {r : ℕ}
    (hr : r < n) :
    lrHiveFun T (Vertex.ofChart n (r + 1) (r + 1) le_rfl hr) -
        lrHiveFun T (Vertex.ofChart n r r le_rfl (by omega)) = (γ.shape.rowLen r : ℤ) := by
  have h1 := lrHiveFun_step_i T (i := r) (j := r + 1) (Nat.lt_succ_self r) hr
  have h2 := lrHiveFun_step_j T (i := r) (j := r) le_rfl hr
  have hdiag : ∑ s ∈ Finset.range (r + 1), (T.val.rowCount s r : ℤ) = (T.val.rowCount r r : ℤ) := by
    rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
    intro s hs
    simp [T.rowCount_eq_zero_of_lt (Finset.mem_range.mp hs)]
  have hrow : ∑ k ∈ Finset.range (r + 1), T.val.rowCount r k =
      γ.shape.rowLen r - lam.shape.rowLen r :=
    T.val.sum_range_rowCount_of_forall_lt fun j _ _ => Nat.lt_succ_of_le (T.entry_le r j)
  have hrowZ : (lam.shape.rowLen r : ℤ) + ∑ k ∈ Finset.range (r + 1), (T.val.rowCount r k : ℤ) =
      (γ.shape.rowLen r : ℤ) := by
    have hle := YoungDiagram.rowLen_le_of_le T.val.le r
    have hrow' : ∑ k ∈ Finset.range (r + 1), (T.val.rowCount r k : ℤ) =
        ((γ.shape.rowLen r - lam.shape.rowLen r : ℕ) : ℤ) := by exact_mod_cast hrow
    rw [hrow']; omega
  rw [Finset.sum_range_succ] at hrowZ
  linarith

private theorem boundary_lrHiveFun (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (hγ : γ.IsPolynomial) (T : LRTableau lam.shape γ.shape μ.shape) :
    (Hive.mk (lrHiveFun T) (by simp [lrHiveFun])
      (fun hr => (isRhombusConcave_def _).mp (isRhombusConcave_lrHiveFun T) hr)).boundary =
        productBoundary lam μ γ := by
  ext s i
  fin_cases s
  · simp only [Fin.zero_eta, Fin.isValue, boundary_apply, productBoundary_zero]
    have hsucc : Vertex.edgePoint n 0 i.succ =
        Vertex.ofChart n 0 (i.val + 1) (Nat.zero_le _) i.isLt :=
      (Vertex.ofChart_zero_left n (i.val + 1) i.isLt).symm
    have hcast : Vertex.edgePoint n 0 i.castSucc =
        Vertex.ofChart n 0 i.val (Nat.zero_le _) i.isLt.le :=
      (Vertex.ofChart_zero_left n i.val i.isLt.le).symm
    rw [hsucc, hcast, mk_apply, mk_apply, lrHiveFun_step_j T (Nat.zero_le _) i.isLt,
      Finset.sum_range_zero, add_zero, DominantWeight.natCast_rowLen_shape hlam i]
  · simp only [Fin.mk_one, Fin.isValue, boundary_apply, productBoundary_one]
    have hsucc : Vertex.edgePoint n 1 i.succ = Vertex.ofChart n (i.val + 1) n i.isLt le_rfl :=
      (Vertex.ofChart_right n (i.val + 1) i.isLt).symm
    have hcast : Vertex.edgePoint n 1 i.castSucc = Vertex.ofChart n i.val n i.isLt.le le_rfl :=
      (Vertex.ofChart_right n i.val i.isLt.le).symm
    rw [hsucc, hcast, mk_apply, mk_apply, lrHiveFun_step_i T i.isLt le_rfl]
    have hcont : ∑ r ∈ Finset.range n, T.val.rowCount r i.val = μ.shape.rowLen i.val := by
      rw [T.val.sum_range_rowCount_eq_content i.val (DominantWeight.colLen_zero_shape_le γ)]
      exact congrFun T.property.1 i.val
    have hcontZ : ∑ r ∈ Finset.range n, (T.val.rowCount r i.val : ℤ) = (μ.shape.rowLen i.val : ℤ) :=
      by exact_mod_cast hcont
    rw [hcontZ, DominantWeight.natCast_rowLen_shape hμ i]
  · simp only [Fin.reduceFinMk, Fin.isValue, boundary_apply, productBoundary_two,
      DominantWeight.dual_apply]
    have hsucc : Vertex.edgePoint n 2 i.succ =
        Vertex.ofChart n i.rev.val i.rev.val le_rfl i.rev.isLt.le := by
      rw [Vertex.ofChart_self]; congr 1; ext; simp [Fin.val_rev]; omega
    have hcast : Vertex.edgePoint n 2 i.castSucc =
        Vertex.ofChart n (i.rev.val + 1) (i.rev.val + 1) le_rfl i.rev.isLt := by
      rw [Vertex.ofChart_self]; congr 1; ext; simp [Fin.val_rev]; omega
    rw [hsucc, hcast, mk_apply, mk_apply]
    have hdiag := lrHiveFun_step_diag T i.rev.isLt
    rw [DominantWeight.natCast_rowLen_shape hγ i.rev] at hdiag
    linarith

/-- The fixed-boundary integer hive attached to a Littlewood–Richardson tableau `T` on polynomial
dominant weights `λ, μ, γ`. -/
def hiveOfLRTableau (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) : FixedIntegerHive (productBoundary lam μ γ) :=
  ⟨⟨lrHiveFun T, by simp [lrHiveFun],
      fun hr => (isRhombusConcave_def _).mp (isRhombusConcave_lrHiveFun T) hr⟩,
    boundary_lrHiveFun hlam hμ hγ T⟩

private theorem hiveOfLRTableau_apply (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (hγ : γ.IsPolynomial) (T : LRTableau lam.shape γ.shape μ.shape) (p : Vertex n) :
    (hiveOfLRTableau hlam hμ hγ T).val p = lrHiveFun T p :=
  rfl

/-- Evaluating `hiveOfLRTableau` at chart coordinates `(i, j)`. -/
@[simp] theorem hiveOfLRTableau_apply_ofChart (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (hγ : γ.IsPolynomial) (T : LRTableau lam.shape γ.shape μ.shape) {i j : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) :
    (hiveOfLRTableau hlam hμ hγ T).val (Vertex.ofChart n i j hij hjn) =
      (∑ r ∈ Finset.range j, (lam.shape.rowLen r : ℤ)) +
        ∑ k ∈ Finset.range i, ∑ r ∈ Finset.range j, (T.val.rowCount r k : ℤ) :=
  lrHiveFun_ofChart T hij hjn

end ForwardMap

/-! ### Inverse map: integer hives to Littlewood–Richardson tableaux -/

section InverseMap

variable {n : ℕ}

/-- Integer count of letter `k` in row `r` extracted from an integer hive `h`: upright-rhombus
slack for `k < r < n`, diagonal step `h(r + 1, r + 1) - h(r, r + 1)` for `k = r < n`, and `0`
otherwise. -/
private def hiveEntryInt (h : IntegerHive n) (r k : ℕ) : ℤ :=
  if hr : r < n then
    if hk : k < r then
      h (Vertex.ofChart n (k + 1) (r + 1) (by omega) hr) -
        h (Vertex.ofChart n k (r + 1) (by omega) hr) -
        h (Vertex.ofChart n (k + 1) r hk hr.le) +
        h (Vertex.ofChart n k r hk.le hr.le)
    else if k = r then
      h (Vertex.ofChart n (r + 1) (r + 1) le_rfl hr) -
        h (Vertex.ofChart n r (r + 1) (Nat.le_succ r) hr)
    else 0
  else 0

private def hiveEntryNat (h : IntegerHive n) (r k : ℕ) : ℕ := (hiveEntryInt h r k).toNat

private theorem hiveEntryInt_eq_zero_of_le (h : IntegerHive n) {r k : ℕ} (hr : n ≤ r) :
    hiveEntryInt h r k = 0 := by
  simp [hiveEntryInt, Nat.not_lt.mpr hr]

private theorem hiveEntryInt_eq_zero_of_lt (h : IntegerHive n) {r k : ℕ} (hk : r < k) :
    hiveEntryInt h r k = 0 := by
  simp [hiveEntryInt, Nat.not_lt.mpr hk.le, hk.ne']

private theorem hiveEntryInt_eq_zero_of_le_right (h : IntegerHive n) {r k : ℕ} (hk : n ≤ k) :
    hiveEntryInt h r k = 0 := by
  by_cases hr : r < n
  · exact hiveEntryInt_eq_zero_of_lt h (hr.trans_le hk)
  · exact hiveEntryInt_eq_zero_of_le h (Nat.le_of_not_lt hr)

private theorem hiveEntryInt_add_affine_of_lt (h : IntegerHive n) (a b : ℤ)
    {r k : ℕ} (hkr : k < r) (hr : r < n) :
    hiveEntryInt (h + affine n a b) r k = hiveEntryInt h r k := by
  simp only [hiveEntryInt, hr, ↓reduceDIte, hkr, Hive.add_apply, Hive.affine_apply,
    Vertex.ofChart_y, Vertex.ofChart_z, nsmul_eq_mul]
  zify [show k ≤ r from hkr.le, show k + 1 ≤ r from hkr,
    show k ≤ r + 1 from by omega, show k + 1 ≤ r + 1 from by omega]
  ring

private theorem hiveEntryInt_add_affine_diag (h : IntegerHive n) (a b : ℤ)
    {r : ℕ} (hr : r < n) :
    hiveEntryInt (h + affine n a (a + b)) r r = hiveEntryInt h r r + b := by
  simp only [hiveEntryInt, hr, ↓reduceDIte, lt_irrefl, ↓reduceIte, Hive.add_apply,
    Hive.affine_apply, Vertex.ofChart_y, Vertex.ofChart_z, nsmul_eq_mul, Nat.sub_self,
    Nat.add_sub_cancel_left]
  push_cast
  ring

/-- Column telescoping of `hiveEntryInt`: for `k < j ≤ n`, summing `hiveEntryInt h r k` over
`r < j` gives `h(k + 1, j) - h(k, j)`. -/
private theorem sum_range_hiveEntryInt_col (h : IntegerHive n) {k j : ℕ}
    (hkj : k < j) (hjn : j ≤ n) :
    ∑ r ∈ Finset.range j, hiveEntryInt h r k =
      h (Vertex.ofChart n (k + 1) j hkj hjn) - h (Vertex.ofChart n k j hkj.le hjn) := by
  induction j with
  | zero => omega
  | succ m ih =>
    have hm : m < n := hjn
    rw [Finset.sum_range_succ]
    rcases (Nat.lt_succ_iff.mp hkj).lt_or_eq with hkm | rfl
    · rw [ih hkm (by omega)]
      simp only [hiveEntryInt, hm, ↓reduceDIte, hkm]
      abel
    · rw [Finset.sum_eq_zero fun r hr =>
        hiveEntryInt_eq_zero_of_lt h (Finset.mem_range.mp hr), zero_add]
      simp [hiveEntryInt, hm]

/-- Row telescoping of `hiveEntryInt` up to `i ≤ r < n`. -/
private theorem sum_range_hiveEntryInt_row_le (h : IntegerHive n) {r i : ℕ}
    (hir : i ≤ r) (hr : r < n) :
    ∑ k ∈ Finset.range i, hiveEntryInt h r k =
      (h (Vertex.ofChart n i (r + 1) (by omega) hr) - h (Vertex.ofChart n i r hir hr.le)) -
        (h (Vertex.ofChart n 0 (r + 1) (Nat.zero_le _) hr) -
          h (Vertex.ofChart n 0 r (Nat.zero_le _) hr.le)) := by
  induction i with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have hm : m < r := by omega
    simp only [hiveEntryInt, hr, ↓reduceDIte, hm]
    abel

/-- Full row sum of `hiveEntryInt` for `r < n` and `r + 1 ≤ i`. -/
private theorem sum_range_hiveEntryInt_row_full (h : IntegerHive n) {r i : ℕ}
    (hri : r + 1 ≤ i) (hr : r < n) :
    ∑ k ∈ Finset.range i, hiveEntryInt h r k =
      (h (Vertex.ofChart n (r + 1) (r + 1) le_rfl hr) - h (Vertex.ofChart n r r le_rfl hr.le)) -
        (h (Vertex.ofChart n 0 (r + 1) (Nat.zero_le _) hr) -
          h (Vertex.ofChart n 0 r (Nat.zero_le _) hr.le)) := by
  rw [sum_range_eq_of_eq_zero hri fun k hk _ => hiveEntryInt_eq_zero_of_lt h (by omega),
    Finset.sum_range_succ, sum_range_hiveEntryInt_row_le h le_rfl hr]
  simp only [hiveEntryInt, hr, ↓reduceDIte, lt_irrefl, ↓reduceIte]
  abel

variable {lam μ γ : DominantWeight n}

/-- Every extracted integer entry `hiveEntryInt h.val r k` is nonnegative when `μ` is polynomial. -/
private theorem hiveEntryInt_nonneg (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r k : ℕ) :
    0 ≤ hiveEntryInt h.val r k := by
  by_cases hr : r < n
  · by_cases hk : k < r
    · simp only [hiveEntryInt, hr, ↓reduceDIte, hk]
      linarith [h.val.le_of_isRhombus (isRhombus_ofChart_diag_y hk hr)]
    · by_cases hkeq : k = r
      · subst k
        -- Prove `0 ≤ hiveEntryInt h.val r r` by downward induction on `r` from `n - 1`.
        suffices ∀ d r, r + d + 1 = n → 0 ≤ hiveEntryInt h.val r r from
          this (n - 1 - r) r (by omega)
        intro d
        induction d with
        | zero =>
          intro r hdn
          have hr' : r < n := by omega
          have h1 : hiveEntryInt h.val r r =
              h.val (Vertex.ofChart n (r + 1) n (by omega) le_rfl) -
                h.val (Vertex.ofChart n r n (by omega) le_rfl) := by
            simp only [hiveEntryInt, hr', ↓reduceDIte, lt_irrefl, ↓reduceIte]
            congr 2 <;> simp [hdn]
          rw [h1, step_ofChart_right_of_productBoundary h hr']
          exact (DominantWeight.isPolynomial_def _).mp hμ ⟨r, hr'⟩
        | succ d ih =>
          intro r hdn
          have hr' : r < n := by omega
          have hr1 : r + 1 < n := by omega
          have hstep : hiveEntryInt h.val (r + 1) (r + 1) ≤ hiveEntryInt h.val r r := by
            simp only [hiveEntryInt, hr', hr1, ↓reduceDIte, lt_irrefl, ↓reduceIte]
            linarith [h.val.le_of_isRhombus
              (isRhombus_ofChart_diag_z (i := r) (j := r + 1) (Nat.lt_succ_self r) hr1)]
          exact (ih (r + 1) (by omega)).trans hstep
      · simp [hiveEntryInt, hr, hk, hkeq]
  · simp [hiveEntryInt, hr]

private theorem natCast_hiveEntryNat (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r k : ℕ) :
    (hiveEntryNat h.val r k : ℤ) = hiveEntryInt h.val r k :=
  Int.toNat_of_nonneg (hiveEntryInt_nonneg hμ h r k)

private theorem natCast_sum_hiveEntryNat {ι : Type*} (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (s : Finset ι) (f g : ι → ℕ) :
    ((∑ x ∈ s, hiveEntryNat h.val (f x) (g x) : ℕ) : ℤ) =
      ∑ x ∈ s, hiveEntryInt h.val (f x) (g x) := by
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl fun x _ => natCast_hiveEntryNat hμ h (f x) (g x)

private theorem shape_le_of_fixedIntegerHive (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    lam.shape ≤ γ.shape := by
  have hγ : γ.IsPolynomial := isPolynomial_of_productBoundary h.property hlam hμ
  refine YoungDiagram.le_of_forall_rowLen_le fun r => ?_
  by_cases hr : r < n
  · have hfull := sum_range_hiveEntryInt_row_full h.val (i := n) hr hr
    rw [step_ofChart_self_of_productBoundary h hr,
      step_ofChart_zero_left_of_productBoundary h hr] at hfull
    have hnn : 0 ≤ ∑ k ∈ Finset.range n, hiveEntryInt h.val r k :=
      Finset.sum_nonneg fun k _ => hiveEntryInt_nonneg hμ h r k
    have h1 : (lam.shape.rowLen r : ℤ) = lam.val ⟨r, hr⟩ :=
      DominantWeight.natCast_rowLen_shape hlam ⟨r, hr⟩
    have h2 : (γ.shape.rowLen r : ℤ) = γ.val ⟨r, hr⟩ :=
      DominantWeight.natCast_rowLen_shape hγ ⟨r, hr⟩
    omega
  · simp [DominantWeight.rowLen_shape_eq_zero_of_le _ (Nat.le_of_not_lt hr)]

private theorem sum_range_hiveEntryNat_row (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r : ℕ) :
    ∑ k ∈ Finset.range n, hiveEntryNat h.val r k = γ.shape.rowLen r - lam.shape.rowLen r := by
  have hγ : γ.IsPolynomial := isPolynomial_of_productBoundary h.property hlam hμ
  by_cases hr : r < n
  · have hfull := sum_range_hiveEntryInt_row_full h.val (i := n) hr hr
    rw [step_ofChart_self_of_productBoundary h hr,
      step_ofChart_zero_left_of_productBoundary h hr] at hfull
    have hZ : ((∑ k ∈ Finset.range n, hiveEntryNat h.val r k : ℕ) : ℤ) =
        ∑ k ∈ Finset.range n, hiveEntryInt h.val r k :=
      natCast_sum_hiveEntryNat hμ h (Finset.range n) (fun _ => r) (fun k => k)
    have h1 : (lam.shape.rowLen r : ℤ) = lam.val ⟨r, hr⟩ :=
      DominantWeight.natCast_rowLen_shape hlam ⟨r, hr⟩
    have h2 : (γ.shape.rowLen r : ℤ) = γ.val ⟨r, hr⟩ :=
      DominantWeight.natCast_rowLen_shape hγ ⟨r, hr⟩
    have := YoungDiagram.rowLen_le_of_le (shape_le_of_fixedIntegerHive hlam hμ h) r
    omega
  · have hnr : n ≤ r := Nat.le_of_not_lt hr
    simp [hiveEntryNat, hiveEntryInt_eq_zero_of_le h.val hnr,
      DominantWeight.rowLen_shape_eq_zero_of_le _ hnr]

private theorem sum_range_hiveEntryNat_col (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (k : ℕ) :
    ∑ r ∈ Finset.range n, hiveEntryNat h.val r k = μ.shape.rowLen k := by
  by_cases hk : k < n
  · have hZ : ((∑ r ∈ Finset.range n, hiveEntryNat h.val r k : ℕ) : ℤ) =
        ∑ r ∈ Finset.range n, hiveEntryInt h.val r k :=
      natCast_sum_hiveEntryNat hμ h (Finset.range n) (fun r => r) (fun _ => k)
    have hμk : (μ.shape.rowLen k : ℤ) = μ.val ⟨k, hk⟩ :=
      DominantWeight.natCast_rowLen_shape hμ ⟨k, hk⟩
    rw [sum_range_hiveEntryInt_col h.val hk le_rfl,
      step_ofChart_right_of_productBoundary h hk, ← hμk] at hZ
    exact Int.ofNat.inj hZ
  · have hnk : n ≤ k := Nat.le_of_not_lt hk
    simp [hiveEntryNat, hiveEntryInt_eq_zero_of_le_right h.val hnk,
      DominantWeight.rowLen_shape_eq_zero_of_le _ hnk]

private theorem hiveEntryNat_col_strict (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r x : ℕ) :
    lam.shape.rowLen (r + 1) + ∑ k ∈ Finset.range (x + 1), hiveEntryNat h.val (r + 1) k ≤
      lam.shape.rowLen r + ∑ k ∈ Finset.range x, hiveEntryNat h.val r k := by
  by_cases hr1 : r + 1 < n
  · have hr : r < n := by omega
    suffices ((lam.shape.rowLen (r + 1) : ℤ) +
        ∑ k ∈ Finset.range (x + 1), hiveEntryInt h.val (r + 1) k) ≤
        (lam.shape.rowLen r : ℤ) + ∑ k ∈ Finset.range x, hiveEntryInt h.val r k by
      have hL := natCast_sum_hiveEntryNat hμ h (Finset.range (x + 1)) (fun _ => r + 1) (fun k => k)
      have hR := natCast_sum_hiveEntryNat hμ h (Finset.range x) (fun _ => r) (fun k => k)
      omega
    rw [DominantWeight.natCast_rowLen_shape hlam ⟨r + 1, hr1⟩,
      DominantWeight.natCast_rowLen_shape hlam ⟨r, hr⟩]
    rcases le_or_gt x r with hxr | hrx
    · rw [sum_range_hiveEntryInt_row_le h.val (by omega : x + 1 ≤ r + 1) hr1,
        sum_range_hiveEntryInt_row_le h.val hxr hr,
        step_ofChart_zero_left_of_productBoundary h hr1,
        step_ofChart_zero_left_of_productBoundary h hr]
      linarith [h.val.le_of_isRhombus (isRhombus_ofChart_diag_x hxr (by omega : r + 2 ≤ n))]
    · rw [sum_range_hiveEntryInt_row_full h.val (by omega : r + 2 ≤ x + 1) hr1,
        sum_range_hiveEntryInt_row_full h.val hrx hr,
        step_ofChart_self_of_productBoundary h hr1, step_ofChart_self_of_productBoundary h hr,
        step_ofChart_zero_left_of_productBoundary h hr1,
        step_ofChart_zero_left_of_productBoundary h hr]
      have hanti : γ.val ⟨r + 1, hr1⟩ ≤ γ.val ⟨r, hr⟩ :=
        γ.antitone (Fin.mk_le_mk.mpr (Nat.le_succ r))
      linarith
  · have hnr : n ≤ r + 1 := Nat.le_of_not_lt hr1
    have h0 : ∑ k ∈ Finset.range (x + 1), hiveEntryNat h.val (r + 1) k = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hiveEntryNat, hiveEntryInt_eq_zero_of_le h.val hnr]
    rw [DominantWeight.rowLen_shape_eq_zero_of_le _ hnr, h0, add_zero]
    exact Nat.zero_le _

private theorem hiveEntryNat_lattice (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (k x : ℕ) :
    ∑ r ∈ Finset.range (x + 1), hiveEntryNat h.val r (k + 1) ≤
      ∑ r ∈ Finset.range x, hiveEntryNat h.val r k := by
  suffices ∑ r ∈ Finset.range (x + 1), hiveEntryInt h.val r (k + 1) ≤
      ∑ r ∈ Finset.range x, hiveEntryInt h.val r k by
    have hL := natCast_sum_hiveEntryNat hμ h (Finset.range (x + 1)) (fun r => r) (fun _ => k + 1)
    have hR := natCast_sum_hiveEntryNat hμ h (Finset.range x) (fun r => r) (fun _ => k)
    omega
  rcases le_or_gt x k with hxk | hkx
  · rw [Finset.sum_eq_zero fun r hr => hiveEntryInt_eq_zero_of_lt h.val (by
      have := Finset.mem_range.mp hr; omega)]
    exact Finset.sum_nonneg fun r _ => hiveEntryInt_nonneg hμ h r k
  · by_cases hk1 : k + 1 < n
    · rcases le_or_gt (x + 1) n with hx1 | hnx
      · rw [sum_range_hiveEntryInt_col h.val (by omega : k + 1 < x + 1) hx1,
          sum_range_hiveEntryInt_col h.val hkx (by omega : x ≤ n)]
        linarith [h.val.le_of_isRhombus (isRhombus_ofChart_diag_z hkx hx1)]
      · rw [sum_range_eq_of_eq_zero (by omega : n ≤ x + 1) fun r hr _ =>
              hiveEntryInt_eq_zero_of_le h.val hr,
          sum_range_eq_of_eq_zero (by omega : n ≤ x) fun r hr _ =>
              hiveEntryInt_eq_zero_of_le h.val hr,
          sum_range_hiveEntryInt_col h.val hk1 le_rfl,
          sum_range_hiveEntryInt_col h.val (by omega : k < n) le_rfl,
          step_ofChart_right_of_productBoundary h hk1,
          step_ofChart_right_of_productBoundary h (by omega : k < n)]
        exact μ.antitone (Fin.mk_le_mk.mpr (Nat.le_succ k))
    · rw [Finset.sum_eq_zero fun r _ =>
        hiveEntryInt_eq_zero_of_le_right h.val (Nat.le_of_not_lt hk1)]
      exact Finset.sum_nonneg fun r _ => hiveEntryInt_nonneg hμ h r k

/-- The Littlewood–Richardson tableau extracted from a fixed-boundary integer hive `h` on
polynomial dominant weights `λ, μ` (with `γ` automatically polynomial from the existence of `h`). -/
def lrTableauOfHive (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) : LRTableau lam.shape γ.shape μ.shape :=
  let T : SkewSemistandardYoungTableau lam.shape γ.shape :=
    SkewSemistandardYoungTableau.ofRowCount
      (shape_le_of_fixedIntegerHive hlam hμ h) n (hiveEntryNat h.val)
      (sum_range_hiveEntryNat_row hlam hμ h)
      (hiveEntryNat_col_strict hlam hμ h)
  have hrc : ∀ r k, T.rowCount r k = hiveEntryNat h.val r k :=
    SkewSemistandardYoungTableau.rowCount_ofRowCount _ _ _ fun r l hl => by
      simp [hiveEntryNat, hiveEntryInt_eq_zero_of_le_right h.val hl]
  ⟨T, funext fun k => by
      rw [← T.sum_range_rowCount_eq_content k (DominantWeight.colLen_zero_shape_le γ)]
      simp_rw [hrc]
      exact sum_range_hiveEntryNat_col hμ h k,
    T.isLatticeWord_readingWord_iff.mpr fun k x => by
      simp_rw [hrc]; exact hiveEntryNat_lattice hμ h k x⟩

private theorem rowCount_lrTableauOfHive (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r k : ℕ) :
    (lrTableauOfHive hlam hμ h).val.rowCount r k = (hiveEntryInt h.val r k).toNat :=
  SkewSemistandardYoungTableau.rowCount_ofRowCount _ _ _ (fun r l hl => by
    simp [hiveEntryNat, hiveEntryInt_eq_zero_of_le_right h.val hl]) r k

/-- Below the diagonal (`k < r < n`), the multiplicity of letter `k` in row `r` of
`lrTableauOfHive hlam hμ h` is the upright-rhombus slack of `h` at `(k, r)`. -/
theorem rowCount_lrTableauOfHive_of_lt (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) {r k : ℕ} (hkr : k < r) (hr : r < n) :
    ((lrTableauOfHive hlam hμ h).val.rowCount r k : ℤ) =
      h.val (Vertex.ofChart n (k + 1) (r + 1) (by omega) hr) -
        h.val (Vertex.ofChart n k (r + 1) (by omega) hr) -
        h.val (Vertex.ofChart n (k + 1) r hkr hr.le) +
        h.val (Vertex.ofChart n k r hkr.le hr.le) := by
  rw [rowCount_lrTableauOfHive, Int.toNat_of_nonneg (hiveEntryInt_nonneg hμ h r k)]
  simp only [hiveEntryInt, hr, ↓reduceDIte, hkr]

/-- On the diagonal (`r < n`), the multiplicity of letter `r` in row `r` of
`lrTableauOfHive hlam hμ h` is the diagonal step `h(r + 1, r + 1) - h(r, r + 1)`. -/
theorem rowCount_lrTableauOfHive_diag (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) {r : ℕ} (hr : r < n) :
    ((lrTableauOfHive hlam hμ h).val.rowCount r r : ℤ) =
      h.val (Vertex.ofChart n (r + 1) (r + 1) le_rfl hr) -
        h.val (Vertex.ofChart n r (r + 1) (Nat.le_succ r) hr) := by
  rw [rowCount_lrTableauOfHive, Int.toNat_of_nonneg (hiveEntryInt_nonneg hμ h r r)]
  simp [hiveEntryInt, hr]

/-- Above the diagonal (`r < k`), letter `k` does not appear in row `r` of
`lrTableauOfHive hlam hμ h`. -/
@[simp] theorem rowCount_lrTableauOfHive_eq_zero_of_lt (hlam : lam.IsPolynomial)
    (hμ : μ.IsPolynomial) (h : FixedIntegerHive (productBoundary lam μ γ)) {r k : ℕ}
    (hrk : r < k) :
    (lrTableauOfHive hlam hμ h).val.rowCount r k = 0 :=
  (lrTableauOfHive hlam hμ h).rowCount_eq_zero_of_lt hrk

/-- Past row `n - 1` (`n ≤ r`), `lrTableauOfHive hlam hμ h` has no entries. -/
@[simp] theorem rowCount_lrTableauOfHive_eq_zero_of_le (hlam : lam.IsPolynomial)
    (hμ : μ.IsPolynomial) (h : FixedIntegerHive (productBoundary lam μ γ)) {r k : ℕ}
    (hnr : n ≤ r) :
    (lrTableauOfHive hlam hμ h).val.rowCount r k = 0 := by
  rw [rowCount_lrTableauOfHive, hiveEntryInt_eq_zero_of_le h.val hnr, Int.toNat_zero]

/-- Letters `k ≥ n` do not appear in `lrTableauOfHive hlam hμ h`. -/
@[simp] theorem rowCount_lrTableauOfHive_eq_zero_of_le_right (hlam : lam.IsPolynomial)
    (hμ : μ.IsPolynomial) (h : FixedIntegerHive (productBoundary lam μ γ)) {r k : ℕ}
    (hnk : n ≤ k) :
    (lrTableauOfHive hlam hμ h).val.rowCount r k = 0 := by
  rw [rowCount_lrTableauOfHive, hiveEntryInt_eq_zero_of_le_right h.val hnk, Int.toNat_zero]

/-- Partial-sum identity for `lrTableauOfHive`: for `k < j ≤ n`, summing the multiplicity of
letter `k` over rows `0, …, j - 1` gives the horizontal hive increment `h(k + 1, j) - h(k, j)`. -/
theorem sum_range_rowCount_lrTableauOfHive (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) {k j : ℕ}
    (hkj : k < j) (hjn : j ≤ n) :
    ∑ r ∈ Finset.range j, ((lrTableauOfHive hlam hμ h).val.rowCount r k : ℤ) =
      h.val (Vertex.ofChart n (k + 1) j hkj hjn) - h.val (Vertex.ofChart n k j hkj.le hjn) := by
  simp_rw [rowCount_lrTableauOfHive, fun r => Int.toNat_of_nonneg (hiveEntryInt_nonneg hμ h r k)]
  exact sum_range_hiveEntryInt_col h.val hkj hjn

end InverseMap

/-! ### The hive–Littlewood–Richardson bijection (polynomial and signed weights) -/

section Equivalence

variable {n : ℕ}

section FixedWeights

variable {lam μ γ : DominantWeight n}

/-- Evaluating `hiveOfLRTableau` after `lrTableauOfHive` recovers the original integer hive. -/
@[simp] theorem hiveOfLRTableau_lrTableauOfHive (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (hγ : γ.IsPolynomial) (h : FixedIntegerHive (productBoundary lam μ γ)) :
    hiveOfLRTableau hlam hμ hγ (lrTableauOfHive hlam hμ h) = h := by
  refine Subtype.ext (Hive.ext fun p => ?_)
  have hp : p = Vertex.ofChart n p.z (n - p.x) (by have := p.sum_eq; omega)
      (Nat.sub_le n p.x) := (Vertex.ofChart_z_sub_x p).symm
  rw [hp]
  suffices ∀ i j (hij : i ≤ j) (hjn : j ≤ n),
      (hiveOfLRTableau hlam hμ hγ (lrTableauOfHive hlam hμ h)).val
        (Vertex.ofChart n i j hij hjn) = h.val (Vertex.ofChart n i j hij hjn) from
    this p.z (n - p.x) (by have := p.sum_eq; omega) (Nat.sub_le n p.x)
  intro i j hij hjn
  rw [hiveOfLRTableau_apply_ofChart]
  simp only [rowCount_lrTableauOfHive]
  have hcast : ∀ r k, ((hiveEntryInt h.val r k).toNat : ℤ) = hiveEntryInt h.val r k :=
    fun r k => Int.toNat_of_nonneg (hiveEntryInt_nonneg hμ h r k)
  simp_rw [hcast]
  induction i with
  | zero =>
    rw [Finset.sum_range_zero, add_zero]
    induction j with
    | zero => simp [Vertex.ofChart_zero_zero]
    | succ m ih =>
      have hstep := step_ofChart_zero_left_of_productBoundary h hjn
      rw [← DominantWeight.natCast_rowLen_shape hlam ⟨m, hjn⟩] at hstep
      dsimp only at hstep
      rw [Finset.sum_range_succ, ih (by omega) (Nat.zero_le m), ← hstep]
      abel
  | succ m ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih (by omega),
      sum_range_hiveEntryInt_col h.val hij hjn]
    abel

/-- Evaluating `lrTableauOfHive` after `hiveOfLRTableau` recovers the original tableau. -/
@[simp] theorem lrTableauOfHive_hiveOfLRTableau (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (hγ : γ.IsPolynomial) (T : LRTableau lam.shape γ.shape μ.shape) :
    lrTableauOfHive hlam hμ (hiveOfLRTableau hlam hμ hγ T) = T := by
  refine Subtype.ext (SkewSemistandardYoungTableau.eq_of_rowCount_eq fun r k => ?_)
  rw [rowCount_lrTableauOfHive]
  suffices hiveEntryInt (hiveOfLRTableau hlam hμ hγ T).val r k = (T.val.rowCount r k : ℤ) by
    rw [this, Int.toNat_natCast]
  by_cases hr : r < n
  · by_cases hk : k < r
    · simp only [hiveEntryInt, hr, ↓reduceDIte, hk, hiveOfLRTableau_apply]
      have h1 := lrHiveFun_step_i T (i := k) (j := r + 1) (by omega) hr
      have h2 := lrHiveFun_step_i T (i := k) (j := r) hk hr.le
      rw [Finset.sum_range_succ] at h1
      linarith
    · by_cases hkeq : k = r
      · subst k
        simp only [hiveEntryInt, hr, ↓reduceDIte, lt_irrefl, ↓reduceIte, hiveOfLRTableau_apply]
        have h1 := lrHiveFun_step_i T (i := r) (j := r + 1) (Nat.lt_succ_self r) hr
        rw [Finset.sum_range_succ, Finset.sum_eq_zero fun s hs => by
          simp [T.rowCount_eq_zero_of_lt (Finset.mem_range.mp hs)], zero_add] at h1
        exact h1
      · simp only [hiveEntryInt, hr, ↓reduceDIte, hk, hkeq, ↓reduceIte]
        rw [T.rowCount_eq_zero_of_lt (by omega), Nat.cast_zero]
  · rw [hiveEntryInt_eq_zero_of_le _ (Nat.le_of_not_lt hr),
      T.val.rowCount_eq_zero_of_colLen_le
        ((DominantWeight.colLen_zero_shape_le γ).trans (Nat.le_of_not_lt hr)), Nat.cast_zero]

/-- **The hive–Littlewood–Richardson equivalence** (polynomial weights): for polynomial dominant
weights `λ, μ, γ` of `GLₙ`, integer hives with boundary `(λ, μ, γ*)` are in explicit bijection
with Littlewood–Richardson tableaux of skew shape `γ / λ` and content `μ`. -/
def fixedIntegerHiveEquivLRTableau (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (hγ : γ.IsPolynomial) :
    FixedIntegerHive (productBoundary lam μ γ) ≃ LRTableau lam.shape γ.shape μ.shape where
  toFun := lrTableauOfHive hlam hμ
  invFun := hiveOfLRTableau hlam hμ hγ
  left_inv := hiveOfLRTableau_lrTableauOfHive hlam hμ hγ
  right_inv := lrTableauOfHive_hiveOfLRTableau hlam hμ hγ

/-- Forward direction of `fixedIntegerHiveEquivLRTableau`. -/
@[simp] theorem fixedIntegerHiveEquivLRTableau_apply (hlam : lam.IsPolynomial)
    (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    fixedIntegerHiveEquivLRTableau hlam hμ hγ h = lrTableauOfHive hlam hμ h := (rfl)

/-- Inverse direction of `fixedIntegerHiveEquivLRTableau`. -/
@[simp] theorem fixedIntegerHiveEquivLRTableau_symm_apply (hlam : lam.IsPolynomial)
    (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial) (T : LRTableau lam.shape γ.shape μ.shape) :
    (fixedIntegerHiveEquivLRTableau hlam hμ hγ).symm T = hiveOfLRTableau hlam hμ hγ T := (rfl)

/-- For polynomial dominant weights `λ, μ, γ`, `hiveCount (productBoundary λ μ γ)` equals the
Littlewood–Richardson coefficient `Nat.card (LRTableau λ.shape γ.shape μ.shape)`. -/
theorem hiveCount_productBoundary_eq_natCard_lrTableau (hlam : lam.IsPolynomial)
    (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial) :
    hiveCount (productBoundary lam μ γ) = Nat.card (LRTableau lam.shape γ.shape μ.shape) := by
  rw [← natCard_fixedIntegerHive]
  exact Nat.card_congr (fixedIntegerHiveEquivLRTableau hlam hμ hγ)

/-- **Shift-independent hive–Littlewood–Richardson bijection**: for arbitrary signed dominant
weights `λ, μ, γ` and any shifts `a, b ∈ ℤ` rendering `λ + a`, `μ + b`, and `γ + (a + b)`
polynomial, integer hives with boundary `(λ, μ, γ*)` biject with Littlewood–Richardson tableaux
for the shifted shapes. -/
def fixedIntegerHiveEquivLRTableauShift {a b : ℤ}
    (hlam : (lam.shift a).IsPolynomial) (hμ : (μ.shift b).IsPolynomial)
    (hγ : (γ.shift (a + b)).IsPolynomial) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      LRTableau (lam.shift a).shape (γ.shift (a + b)).shape (μ.shift b).shape :=
  (shiftProductBoundaryEquiv lam μ γ a b).trans (fixedIntegerHiveEquivLRTableau hlam hμ hγ)

/-- Forward direction of `fixedIntegerHiveEquivLRTableauShift`. -/
@[simp] theorem fixedIntegerHiveEquivLRTableauShift_apply {a b : ℤ}
    (hlam : (lam.shift a).IsPolynomial) (hμ : (μ.shift b).IsPolynomial)
    (hγ : (γ.shift (a + b)).IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    fixedIntegerHiveEquivLRTableauShift hlam hμ hγ h =
      lrTableauOfHive hlam hμ (shiftProductBoundaryEquiv lam μ γ a b h) := (rfl)

/-- Inverse direction of `fixedIntegerHiveEquivLRTableauShift`. -/
@[simp] theorem fixedIntegerHiveEquivLRTableauShift_symm_apply {a b : ℤ}
    (hlam : (lam.shift a).IsPolynomial) (hμ : (μ.shift b).IsPolynomial)
    (hγ : (γ.shift (a + b)).IsPolynomial)
    (T : LRTableau (lam.shift a).shape (γ.shift (a + b)).shape (μ.shift b).shape) :
    (fixedIntegerHiveEquivLRTableauShift hlam hμ hγ).symm T =
      (shiftProductBoundaryEquiv lam μ γ a b).symm (hiveOfLRTableau hlam hμ hγ T) := (rfl)

/-- Canonical transport between shifted Littlewood–Richardson tableaux attached to two admissible
shift pairs `(a₁, b₁)` and `(a₂, b₂)` for the same weights `λ, μ, γ`. -/
def lrTableauShiftEquiv {a₁ b₁ a₂ b₂ : ℤ}
    (hlam₁ : (lam.shift a₁).IsPolynomial) (hμ₁ : (μ.shift b₁).IsPolynomial)
    (hγ₁ : (γ.shift (a₁ + b₁)).IsPolynomial)
    (hlam₂ : (lam.shift a₂).IsPolynomial) (hμ₂ : (μ.shift b₂).IsPolynomial)
    (hγ₂ : (γ.shift (a₂ + b₂)).IsPolynomial) :
    LRTableau (lam.shift a₁).shape (γ.shift (a₁ + b₁)).shape (μ.shift b₁).shape ≃
      LRTableau (lam.shift a₂).shape (γ.shift (a₂ + b₂)).shape (μ.shift b₂).shape :=
  (fixedIntegerHiveEquivLRTableauShift hlam₁ hμ₁ hγ₁).symm.trans
    (fixedIntegerHiveEquivLRTableauShift hlam₂ hμ₂ hγ₂)

/-- Transporting along identical shift pairs is the identity equivalence. -/
@[simp] theorem lrTableauShiftEquiv_refl {a b : ℤ}
    (hlam : (lam.shift a).IsPolynomial) (hμ : (μ.shift b).IsPolynomial)
    (hγ : (γ.shift (a + b)).IsPolynomial) :
    lrTableauShiftEquiv hlam hμ hγ hlam hμ hγ = Equiv.refl _ :=
  Equiv.symm_trans_self _

/-- The inverse of `lrTableauShiftEquiv` reverses the two shift pairs. -/
@[simp] theorem lrTableauShiftEquiv_symm {a₁ b₁ a₂ b₂ : ℤ}
    (hlam₁ : (lam.shift a₁).IsPolynomial) (hμ₁ : (μ.shift b₁).IsPolynomial)
    (hγ₁ : (γ.shift (a₁ + b₁)).IsPolynomial)
    (hlam₂ : (lam.shift a₂).IsPolynomial) (hμ₂ : (μ.shift b₂).IsPolynomial)
    (hγ₂ : (γ.shift (a₂ + b₂)).IsPolynomial) :
    (lrTableauShiftEquiv hlam₁ hμ₁ hγ₁ hlam₂ hμ₂ hγ₂).symm =
      lrTableauShiftEquiv hlam₂ hμ₂ hγ₂ hlam₁ hμ₁ hγ₁ :=
  Equiv.ext fun _ => rfl

/-- Composing two `lrTableauShiftEquiv` transports collapses to the direct transport. -/
@[simp] theorem lrTableauShiftEquiv_trans {a₁ b₁ a₂ b₂ a₃ b₃ : ℤ}
    (hlam₁ : (lam.shift a₁).IsPolynomial) (hμ₁ : (μ.shift b₁).IsPolynomial)
    (hγ₁ : (γ.shift (a₁ + b₁)).IsPolynomial)
    (hlam₂ : (lam.shift a₂).IsPolynomial) (hμ₂ : (μ.shift b₂).IsPolynomial)
    (hγ₂ : (γ.shift (a₂ + b₂)).IsPolynomial)
    (hlam₃ : (lam.shift a₃).IsPolynomial) (hμ₃ : (μ.shift b₃).IsPolynomial)
    (hγ₃ : (γ.shift (a₃ + b₃)).IsPolynomial) :
    (lrTableauShiftEquiv hlam₁ hμ₁ hγ₁ hlam₂ hμ₂ hγ₂).trans
        (lrTableauShiftEquiv hlam₂ hμ₂ hγ₂ hlam₃ hμ₃ hγ₃) =
      lrTableauShiftEquiv hlam₁ hμ₁ hγ₁ hlam₃ hμ₃ hγ₃ := by
  ext T
  simp [lrTableauShiftEquiv]

/-- `lrTableauShiftEquiv` intertwines `fixedIntegerHiveEquivLRTableauShift` across admissible shift
pairs. -/
theorem lrTableauShiftEquiv_fixedIntegerHiveEquivLRTableauShift {a₁ b₁ a₂ b₂ : ℤ}
    (hlam₁ : (lam.shift a₁).IsPolynomial) (hμ₁ : (μ.shift b₁).IsPolynomial)
    (hγ₁ : (γ.shift (a₁ + b₁)).IsPolynomial)
    (hlam₂ : (lam.shift a₂).IsPolynomial) (hμ₂ : (μ.shift b₂).IsPolynomial)
    (hγ₂ : (γ.shift (a₂ + b₂)).IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    lrTableauShiftEquiv hlam₁ hμ₁ hγ₁ hlam₂ hμ₂ hγ₂
        (fixedIntegerHiveEquivLRTableauShift hlam₁ hμ₁ hγ₁ h) =
      fixedIntegerHiveEquivLRTableauShift hlam₂ hμ₂ hγ₂ h := by
  simp [lrTableauShiftEquiv]

/-- Inverse commuting law between `lrTableauShiftEquiv` and
`fixedIntegerHiveEquivLRTableauShift`. -/
theorem fixedIntegerHiveEquivLRTableauShift_symm_lrTableauShiftEquiv {a₁ b₁ a₂ b₂ : ℤ}
    (hlam₁ : (lam.shift a₁).IsPolynomial) (hμ₁ : (μ.shift b₁).IsPolynomial)
    (hγ₁ : (γ.shift (a₁ + b₁)).IsPolynomial)
    (hlam₂ : (lam.shift a₂).IsPolynomial) (hμ₂ : (μ.shift b₂).IsPolynomial)
    (hγ₂ : (γ.shift (a₂ + b₂)).IsPolynomial)
    (T : LRTableau (lam.shift a₁).shape (γ.shift (a₁ + b₁)).shape (μ.shift b₁).shape) :
    (fixedIntegerHiveEquivLRTableauShift hlam₂ hμ₂ hγ₂).symm
        (lrTableauShiftEquiv hlam₁ hμ₁ hγ₁ hlam₂ hμ₂ hγ₂ T) =
      (fixedIntegerHiveEquivLRTableauShift hlam₁ hμ₁ hγ₁).symm T := by
  simp [lrTableauShiftEquiv]

/-- `lrTableauShiftEquiv` preserves all off-diagonal row counts (`r ≠ k`). -/
@[simp] theorem rowCount_lrTableauShiftEquiv_of_ne {a₁ b₁ a₂ b₂ : ℤ}
    (hlam₁ : (lam.shift a₁).IsPolynomial) (hμ₁ : (μ.shift b₁).IsPolynomial)
    (hγ₁ : (γ.shift (a₁ + b₁)).IsPolynomial)
    (hlam₂ : (lam.shift a₂).IsPolynomial) (hμ₂ : (μ.shift b₂).IsPolynomial)
    (hγ₂ : (γ.shift (a₂ + b₂)).IsPolynomial)
    (T : LRTableau (lam.shift a₁).shape (γ.shift (a₁ + b₁)).shape (μ.shift b₁).shape)
    {r k : ℕ} (hrk : r ≠ k) :
    (lrTableauShiftEquiv hlam₁ hμ₁ hγ₁ hlam₂ hμ₂ hγ₂ T).val.rowCount r k =
      T.val.rowCount r k := by
  let h := (fixedIntegerHiveEquivLRTableauShift hlam₁ hμ₁ hγ₁).symm T
  have hT : T = fixedIntegerHiveEquivLRTableauShift hlam₁ hμ₁ hγ₁ h :=
    ((fixedIntegerHiveEquivLRTableauShift hlam₁ hμ₁ hγ₁).apply_symm_apply T).symm
  rw [hT, lrTableauShiftEquiv_fixedIntegerHiveEquivLRTableauShift,
    fixedIntegerHiveEquivLRTableauShift_apply, fixedIntegerHiveEquivLRTableauShift_apply,
    rowCount_lrTableauOfHive, rowCount_lrTableauOfHive]
  by_cases hr : r < n
  · rcases lt_or_gt_of_ne hrk with hlt | hgt
    · rw [hiveEntryInt_eq_zero_of_lt _ hlt, hiveEntryInt_eq_zero_of_lt _ hlt]
    · simp only [shiftProductBoundaryEquiv_apply_val]
      rw [hiveEntryInt_add_affine_of_lt h.val a₂ (a₂ + b₂) hgt hr,
        hiveEntryInt_add_affine_of_lt h.val a₁ (a₁ + b₁) hgt hr]
  · rw [hiveEntryInt_eq_zero_of_le _ (Nat.le_of_not_lt hr),
      hiveEntryInt_eq_zero_of_le _ (Nat.le_of_not_lt hr)]

/-- On the diagonal (`r < n`), `lrTableauShiftEquiv` shifts the multiplicity of letter `r` in row
`r` by the difference `b₂ - b₁` of the second shifts. -/
theorem rowCount_lrTableauShiftEquiv_diag {a₁ b₁ a₂ b₂ : ℤ}
    (hlam₁ : (lam.shift a₁).IsPolynomial) (hμ₁ : (μ.shift b₁).IsPolynomial)
    (hγ₁ : (γ.shift (a₁ + b₁)).IsPolynomial)
    (hlam₂ : (lam.shift a₂).IsPolynomial) (hμ₂ : (μ.shift b₂).IsPolynomial)
    (hγ₂ : (γ.shift (a₂ + b₂)).IsPolynomial)
    (T : LRTableau (lam.shift a₁).shape (γ.shift (a₁ + b₁)).shape (μ.shift b₁).shape)
    {r : ℕ} (hr : r < n) :
    ((lrTableauShiftEquiv hlam₁ hμ₁ hγ₁ hlam₂ hμ₂ hγ₂ T).val.rowCount r r : ℤ) =
      (T.val.rowCount r r : ℤ) + (b₂ - b₁) := by
  let h := (fixedIntegerHiveEquivLRTableauShift hlam₁ hμ₁ hγ₁).symm T
  have hT : T = fixedIntegerHiveEquivLRTableauShift hlam₁ hμ₁ hγ₁ h :=
    ((fixedIntegerHiveEquivLRTableauShift hlam₁ hμ₁ hγ₁).apply_symm_apply T).symm
  rw [hT, lrTableauShiftEquiv_fixedIntegerHiveEquivLRTableauShift,
    fixedIntegerHiveEquivLRTableauShift_apply, fixedIntegerHiveEquivLRTableauShift_apply,
    rowCount_lrTableauOfHive, rowCount_lrTableauOfHive,
    Int.toNat_of_nonneg (hiveEntryInt_nonneg hμ₂ _ r r),
    Int.toNat_of_nonneg (hiveEntryInt_nonneg hμ₁ _ r r),
    shiftProductBoundaryEquiv_apply_val, shiftProductBoundaryEquiv_apply_val,
    hiveEntryInt_add_affine_diag h.val a₂ b₂ hr,
    hiveEntryInt_add_affine_diag h.val a₁ b₁ hr]
  ring

/-- Past row `n - 1` (`n ≤ r`), `lrTableauShiftEquiv` has zero row counts. -/
@[simp] theorem rowCount_lrTableauShiftEquiv_of_le {a₁ b₁ a₂ b₂ : ℤ}
    (hlam₁ : (lam.shift a₁).IsPolynomial) (hμ₁ : (μ.shift b₁).IsPolynomial)
    (hγ₁ : (γ.shift (a₁ + b₁)).IsPolynomial)
    (hlam₂ : (lam.shift a₂).IsPolynomial) (hμ₂ : (μ.shift b₂).IsPolynomial)
    (hγ₂ : (γ.shift (a₂ + b₂)).IsPolynomial)
    (T : LRTableau (lam.shift a₁).shape (γ.shift (a₁ + b₁)).shape (μ.shift b₁).shape)
    {r k : ℕ} (hnr : n ≤ r) :
    (lrTableauShiftEquiv hlam₁ hμ₁ hγ₁ hlam₂ hμ₂ hγ₂ T).val.rowCount r k = 0 :=
  (lrTableauShiftEquiv hlam₁ hμ₁ hγ₁ hlam₂ hμ₂ hγ₂ T).val.rowCount_eq_zero_of_colLen_le
    ((DominantWeight.colLen_zero_shape_le _).trans hnr) k

/-- Characterization of `lrTableauShiftEquiv`: a shifted tableau `T₂` equals
`lrTableauShiftEquiv ... T₁` iff its off-diagonal row counts match `T₁` and its diagonal row
counts for `r < n` shift by `b₂ - b₁`. -/
theorem eq_lrTableauShiftEquiv_iff {a₁ b₁ a₂ b₂ : ℤ}
    (hlam₁ : (lam.shift a₁).IsPolynomial) (hμ₁ : (μ.shift b₁).IsPolynomial)
    (hγ₁ : (γ.shift (a₁ + b₁)).IsPolynomial)
    (hlam₂ : (lam.shift a₂).IsPolynomial) (hμ₂ : (μ.shift b₂).IsPolynomial)
    (hγ₂ : (γ.shift (a₂ + b₂)).IsPolynomial)
    (T₁ : LRTableau (lam.shift a₁).shape (γ.shift (a₁ + b₁)).shape (μ.shift b₁).shape)
    (T₂ : LRTableau (lam.shift a₂).shape (γ.shift (a₂ + b₂)).shape (μ.shift b₂).shape) :
    T₂ = lrTableauShiftEquiv hlam₁ hμ₁ hγ₁ hlam₂ hμ₂ hγ₂ T₁ ↔
      (∀ r k, r ≠ k → T₂.val.rowCount r k = T₁.val.rowCount r k) ∧
        ∀ r < n, (T₂.val.rowCount r r : ℤ) = (T₁.val.rowCount r r : ℤ) + (b₂ - b₁) := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact ⟨fun _ _ hrk => rowCount_lrTableauShiftEquiv_of_ne hlam₁ hμ₁ hγ₁ hlam₂ hμ₂ hγ₂ T₁ hrk,
      fun _ hr => rowCount_lrTableauShiftEquiv_diag hlam₁ hμ₁ hγ₁ hlam₂ hμ₂ hγ₂ T₁ hr⟩
  · rintro ⟨hne, hdiag⟩
    refine Subtype.ext (SkewSemistandardYoungTableau.eq_of_rowCount_eq fun r k => ?_)
    by_cases hrk : r = k
    · subst k
      by_cases hr : r < n
      · have h1 := hdiag r hr
        have h2 := rowCount_lrTableauShiftEquiv_diag hlam₁ hμ₁ hγ₁ hlam₂ hμ₂ hγ₂ T₁ hr
        omega
      · have hnr : n ≤ r := Nat.le_of_not_lt hr
        rw [T₂.val.rowCount_eq_zero_of_colLen_le
            ((DominantWeight.colLen_zero_shape_le _).trans hnr),
          rowCount_lrTableauShiftEquiv_of_le hlam₁ hμ₁ hγ₁ hlam₂ hμ₂ hγ₂ T₁ hnr]
    · rw [hne r k hrk, rowCount_lrTableauShiftEquiv_of_ne hlam₁ hμ₁ hγ₁ hlam₂ hμ₂ hγ₂ T₁ hrk]

/-- Shift-independent cardinality identity for arbitrary signed dominant weights. -/
theorem hiveCount_productBoundary_eq_natCard_lrTableau_of_shift {a b : ℤ}
    (hlam : (lam.shift a).IsPolynomial) (hμ : (μ.shift b).IsPolynomial)
    (hγ : (γ.shift (a + b)).IsPolynomial) :
    hiveCount (productBoundary lam μ γ) =
      Nat.card (LRTableau (lam.shift a).shape (γ.shift (a + b)).shape (μ.shift b).shape) := by
  rw [← natCard_fixedIntegerHive]
  exact Nat.card_congr (fixedIntegerHiveEquivLRTableauShift hlam hμ hγ)

/-- Canonical determinant-shift bijection for arbitrary signed dominant weights `λ, μ, γ` satisfying
the necessary lower-coordinate condition `λ.detShift + μ.detShift ≤ γ.detShift`. -/
def fixedIntegerHiveEquivLRTableauDetShift
    (hshift : lam.detShift + μ.detShift ≤ γ.detShift) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      LRTableau lam.detShiftShape (γ.shift (-(lam.detShift + μ.detShift))).shape
        μ.detShiftShape :=
  (fixedIntegerHiveEquivLRTableauShift (lam := lam) (μ := μ) (γ := γ)
    (a := -lam.detShift) (b := -μ.detShift)
    lam.isPolynomial_shift_neg_detShift μ.isPolynomial_shift_neg_detShift
    (γ.isPolynomial_shift_of_zero_le_detShift_add (by omega))).trans
    (LRTableau.congr lam.shape_shift_neg_detShift
      (congrArg (fun m => (γ.shift m).shape) (neg_add lam.detShift μ.detShift).symm)
      μ.shape_shift_neg_detShift)

/-- Forward direction of `fixedIntegerHiveEquivLRTableauDetShift`. -/
@[simp] theorem fixedIntegerHiveEquivLRTableauDetShift_apply
    (hshift : lam.detShift + μ.detShift ≤ γ.detShift)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    fixedIntegerHiveEquivLRTableauDetShift hshift h =
      LRTableau.congr lam.shape_shift_neg_detShift
        (congrArg (fun m => (γ.shift m).shape) (neg_add lam.detShift μ.detShift).symm)
        μ.shape_shift_neg_detShift
        (lrTableauOfHive lam.isPolynomial_shift_neg_detShift μ.isPolynomial_shift_neg_detShift
          (shiftProductBoundaryEquiv lam μ γ (-lam.detShift) (-μ.detShift) h)) := (rfl)

/-- Inverse direction of `fixedIntegerHiveEquivLRTableauDetShift`. -/
@[simp] theorem fixedIntegerHiveEquivLRTableauDetShift_symm_apply
    (hshift : lam.detShift + μ.detShift ≤ γ.detShift)
    (T : LRTableau lam.detShiftShape (γ.shift (-(lam.detShift + μ.detShift))).shape
      μ.detShiftShape) :
    (fixedIntegerHiveEquivLRTableauDetShift hshift).symm T =
      (shiftProductBoundaryEquiv lam μ γ (-lam.detShift) (-μ.detShift)).symm
        (hiveOfLRTableau lam.isPolynomial_shift_neg_detShift μ.isPolynomial_shift_neg_detShift
          (γ.isPolynomial_shift_of_zero_le_detShift_add (by omega))
          (LRTableau.congr lam.shape_shift_neg_detShift.symm
            (congrArg (fun m => (γ.shift m).shape) (neg_add lam.detShift μ.detShift))
            μ.shape_shift_neg_detShift.symm T)) := by
  simp [fixedIntegerHiveEquivLRTableauDetShift]

/-- Every cell entry of `fixedIntegerHiveEquivLRTableauDetShift hshift h` agrees with the shifted
tableau `lrTableauOfHive` with no shape-cast overhead. -/
theorem fixedIntegerHiveEquivLRTableauDetShift_apply_entry
    (hshift : lam.detShift + μ.detShift ≤ γ.detShift)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (i j : ℕ) :
    (fixedIntegerHiveEquivLRTableauDetShift hshift h).val i j =
      (lrTableauOfHive lam.isPolynomial_shift_neg_detShift μ.isPolynomial_shift_neg_detShift
        (shiftProductBoundaryEquiv lam μ γ (-lam.detShift) (-μ.detShift) h)).val i j := by
  simp

/-- The row counts of `fixedIntegerHiveEquivLRTableauDetShift hshift h` agree with those of the
shifted tableau `lrTableauOfHive`. -/
theorem rowCount_fixedIntegerHiveEquivLRTableauDetShift
    (hshift : lam.detShift + μ.detShift ≤ γ.detShift)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (i k : ℕ) :
    (fixedIntegerHiveEquivLRTableauDetShift hshift h).val.rowCount i k =
      (lrTableauOfHive lam.isPolynomial_shift_neg_detShift μ.isPolynomial_shift_neg_detShift
        (shiftProductBoundaryEquiv lam μ γ (-lam.detShift) (-μ.detShift) h)).val.rowCount i k := by
  simp

end FixedWeights

/-- **Signed hive–Littlewood–Richardson count**: for arbitrary dominant weights `λ, μ, γ`,
`hiveCount (productBoundary λ μ γ)` equals the Littlewood–Richardson coefficient for the
determinant-shifted shapes when `λ.detShift + μ.detShift ≤ γ.detShift`, and `0` otherwise. -/
theorem hiveCount_productBoundary_eq_ite_natCard_lrTableau (lam μ γ : DominantWeight n) :
    hiveCount (productBoundary lam μ γ) =
      if lam.detShift + μ.detShift ≤ γ.detShift then
        Nat.card (LRTableau lam.detShiftShape
          (γ.shift (-(lam.detShift + μ.detShift))).shape μ.detShiftShape)
      else 0 := by
  split_ifs with hshift
  · rw [← natCard_fixedIntegerHive]
    exact Nat.card_congr (fixedIntegerHiveEquivLRTableauDetShift hshift)
  · exact hiveCount_eq_zero_iff.mpr ⟨fun ⟨_, hb⟩ => hshift (detShift_le_of_productBoundary hb)⟩

end Equivalence

end TauCeti.Hive
