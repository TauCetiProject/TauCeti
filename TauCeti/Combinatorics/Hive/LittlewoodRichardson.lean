/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Fibre
public import TauCeti.Combinatorics.Young.LittlewoodRichardson.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import TauCeti.Algebra.BigOperators.Finset.PartialSum

/-!
# The hive-to-Littlewood–Richardson equivalence

In the **product chart** `Vertex.productVertex n i j` (`0 ≤ i ≤ j ≤ n` mapped to the barycentric
point `(n - j, j - i, i)` of `Δₙ`, defined in `TauCeti.Combinatorics.Hive.Lattice`), the three
perimeter sides align directly with the product boundary `(λ, μ, γ*)`:
* `i = 0` runs clockwise along `A → B`, where successive differences record `λ`;
* `j = n` runs clockwise along `B → C`, where successive differences record `μ`;
* the diagonal `i = j` runs counterclockwise along `A → C` (the reverse of `C → A`), so successive
  diagonal values record prefix sums of `γ`.

Every unit rhombus in `Δₙ` belongs to one of three orientations in `(i, j)` coordinates
(`TauCeti.Hive.isRhombusConcave_iff_productVertex` in `TauCeti.Combinatorics.Hive.Basic`),
identifying hive concavity with the three defining conditions of a Littlewood–Richardson tableau `T`
of skew shape `γ / λ` and content `μ` via the row-letter counts `a(r, k) = T.rowCount r k`:
1. **Off-diagonal mixed differences** (`0 ≤ k < r < n`):
   `h(k + 1, r) + h(k, r + 1) ≤ h(k, r) + h(k + 1, r + 1)` expresses nonnegativity of the mixed
   difference `a(r, k) = h(k + 1, r + 1) - h(k, r + 1) - h(k + 1, r) + h(k, r)`.
2. **Row-comparison rhombi** (`0 ≤ x ≤ r` and `r + 2 ≤ n`):
   `h(x, r) + h(x + 1, r + 2) ≤ h(x, r + 1) + h(x + 1, r + 1)` telescopes to column strictness
   `λ_{r + 1} + ∑_{k ≤ x} a(r + 1, k) ≤ λ_r + ∑_{k < x} a(r, k)` when rows are filled weakly
   increasingly via `TauCeti.SkewSemistandardYoungTableau.ofRowCount`.
3. **Ballot rhombi** (`0 ≤ k < x < n`):
   `h(k, x) + h(k + 2, x + 1) ≤ h(k + 1, x) + h(k + 1, x + 1)` telescopes to the Yamanouchi
   lattice-word prefix inequalities `∑_{r ≤ x} a(r, k + 1) ≤ ∑_{r < x} a(r, k)`
   (`TauCeti.SkewSemistandardYoungTableau.isLatticeWord_readingWord_iff`), and along `x = k + 1`
   forces the diagonal counts `a(r, r) = h(r + 1, r + 1) - h(r, r + 1)` to decrease weakly down to
   `a(n - 1, n - 1) = μ_{n - 1}`.

For polynomial dominant weights `λ, μ, γ : DominantWeight n`, the forward sum
`h(i, j) = ∑_{r < j} λ_r + ∑_{k < i} ∑_{k ≤ r < j} a(r, k)` and the inverse difference extraction
assemble into an explicit bijection of objects
`FixedIntegerHive (productBoundary λ μ γ) ≃ LRTableau λ.shape γ.shape μ.shape`
(`TauCeti.Hive.fixedIntegerHiveEquivLRTableau`).

For arbitrary signed dominant weights `λ, μ, γ : DominantWeight n`, composing the affine shift
bijection `TauCeti.Hive.fixedIntegerHiveShiftEquiv` (defined in `TauCeti.Combinatorics.Hive.Fibre`)
with `fixedIntegerHiveEquivLRTableau` yields an explicit bijection with
`LRTableau λ.detShiftShape (γ.shift (-(λ.detShift + μ.detShift))).shape μ.detShiftShape` whenever
`λ.detShift + μ.detShift ≤ γ.detShift` (`TauCeti.Hive.fixedIntegerHiveSignedEquivLRTableau`).

## Main definitions

* `TauCeti.Hive.hiveOfLRTableau` and `TauCeti.Hive.lrTableauOfHive`: explicit mutually inverse
  constructions between Littlewood–Richardson tableaux and normalized integer hives.
* `TauCeti.Hive.fixedIntegerHiveEquivLRTableau`,
  `TauCeti.Hive.fixedIntegerHiveWeightOfShapeEquivLRTableau`, and
  `TauCeti.Hive.fixedIntegerHiveSignedEquivLRTableau`: the polynomial, Young-diagram, and general
  signed hive-to-Littlewood–Richardson equivalences.

## Main results

* `TauCeti.Hive.boundary_hiveOfLRTableau` and `TauCeti.Hive.hiveRowCount_hiveOfLRTableau`:
  boundary and row-count inversion identities for `hiveOfLRTableau`.
* `TauCeti.Hive.rowCount_fixedIntegerHiveWeightOfShapeEquivLRTableau` and
  `TauCeti.Hive.rowCount_fixedIntegerHiveSignedEquivLRTableau`: row-count characterizations of the
  Young-diagram and signed equivalences.

## References

* A. Knutson and T. Tao, *The honeycomb model of GLₙ(ℂ) tensor products I: Proof of the saturation
  conjecture*, J. Amer. Math. Soc. 12 (1999), 1055–1090, Appendix 2.
* A. S. Buch, *The saturation conjecture (after A. Knutson and T. Tao)*, Enseign. Math. (2) 46
  (2000), 43–60, Theorem 3.18.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

/-! ### Forward map: from a Littlewood–Richardson tableau to an integer hive -/

section ForwardMap

private theorem sum_filter_lt_eq_sum_range_rowLen {n : ℕ} {l : DominantWeight n}
    (hl : l.IsPolynomial) {j : ℕ} (hj : j ≤ n) :
    (∑ r : Fin n with r.val < j, l.1 r) = ∑ r ∈ Finset.range j, (l.shape.rowLen r : ℤ) := by
  induction j with
  | zero => simp
  | succ m ih =>
    rw [sum_filter_val_lt_succ (by omega : m < n) l.1, Finset.sum_range_succ, ih (by omega),
      DominantWeight.natCast_rowLen_shape hl ⟨m, by omega⟩]

/-- The lattice function on `Vertex n` attached to a dominant weight `λ` and a skew tableau `T`:
at `productVertex n i j` it sums `λ_r` for `r < j` plus the counts of letters `k < i` in rows
`r < j`. -/
def lrHiveFun {n : ℕ} {inner outer : YoungDiagram} (lam : DominantWeight n)
    (T : SkewSemistandardYoungTableau inner outer) (p : Vertex n) : ℤ :=
  (∑ r : Fin n with r.val < p.y + p.z, lam.1 r) +
    ∑ k ∈ Finset.range p.z, ∑ r ∈ Finset.range (p.y + p.z), (T.rowCount r k : ℤ)

theorem lrHiveFun_apply {n : ℕ} {inner outer : YoungDiagram} (lam : DominantWeight n)
    (T : SkewSemistandardYoungTableau inner outer) (p : Vertex n) :
    lrHiveFun lam T p =
      (∑ r : Fin n with r.val < p.y + p.z, lam.1 r) +
        ∑ k ∈ Finset.range p.z, ∑ r ∈ Finset.range (p.y + p.z), (T.rowCount r k : ℤ) := (rfl)

@[simp] theorem lrHiveFun_cornerA {n : ℕ} {inner outer : YoungDiagram} (lam : DominantWeight n)
    (T : SkewSemistandardYoungTableau inner outer) :
    lrHiveFun lam T (Vertex.cornerA n) = 0 := by
  simp [lrHiveFun]

@[simp] theorem lrHiveFun_productVertex {n i j : ℕ} {inner outer : YoungDiagram}
    (lam : DominantWeight n) (T : SkewSemistandardYoungTableau inner outer)
    (hij : i ≤ j) (hj : j ≤ n) :
    lrHiveFun lam T (Vertex.productVertex n i j hij hj) =
      (∑ r : Fin n with r.val < j, lam.1 r) +
        ∑ k ∈ Finset.range i, ∑ r ∈ Finset.range j, (T.rowCount r k : ℤ) := by
  have hyz : j - i + i = j := by omega
  simp [lrHiveFun, hyz]

/-- On a Littlewood–Richardson tableau, `lrHiveFun` restricts the inner row sum to `k ≤ r < j`:
`h(i, j) = ∑_{r < j} λ_r + ∑_{k < i} ∑_{k ≤ r < j} T.rowCount r k`. -/
theorem lrHiveFun_productVertex_eq_sum_Ico {n i j : ℕ} {inner outer μ : YoungDiagram}
    (lam : DominantWeight n) (T : LRTableau inner outer μ) (hij : i ≤ j) (hj : j ≤ n) :
    lrHiveFun lam T.1 (Vertex.productVertex n i j hij hj) =
      (∑ r : Fin n with r.val < j, lam.1 r) +
        ∑ k ∈ Finset.range i, ∑ r ∈ Finset.Ico k j, (T.1.rowCount r k : ℤ) := by
  rw [lrHiveFun_productVertex]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkj : k ≤ j := (Finset.mem_range.mp hk).le.trans hij
  rw [← Finset.sum_range_add_sum_Ico _ hkj,
    Finset.sum_eq_zero fun r hr => by simp [T.rowCount_eq_zero_of_lt (Finset.mem_range.mp hr)],
    zero_add]

/-- Forward construction of an `IntegerHive n` from a polynomial dominant weight `λ` and a
Littlewood–Richardson tableau `T : LRTableau λ.shape outer μ`. -/
def hiveOfLRTableau {n : ℕ} {outer μ : YoungDiagram} {lam : DominantWeight n}
    (hlam : lam.IsPolynomial) (T : LRTableau lam.shape outer μ) : IntegerHive n where
  value := lrHiveFun lam T.1
  value_cornerA' := lrHiveFun_cornerA lam T.1
  le_of_isRhombus' {a b c d} hr := by
    refine (isRhombusConcave_def _).mp
      ((isRhombusConcave_iff_productVertex (lrHiveFun lam T.1)).mpr ⟨?_, ?_, ?_⟩) hr
    · intro i j hij hj
      simp only [lrHiveFun_productVertex, sum_filter_val_lt_succ (by omega : j < n) lam.1,
        Finset.sum_range_succ]
      linarith [Nat.cast_nonneg (α := ℤ) (T.1.rowCount j i)]
    · intro i j hij hj
      have hj1 : j < n := by omega
      have hj2 : j + 1 < n := by omega
      simp only [lrHiveFun_productVertex, sum_filter_val_lt_succ hj1 lam.1,
        sum_filter_val_lt_succ hj2 lam.1]
      have hlam_j : lam.1 ⟨j, hj1⟩ = (lam.shape.rowLen j : ℤ) :=
        (DominantWeight.natCast_rowLen_shape hlam ⟨j, hj1⟩).symm
      have hlam_j1 : lam.1 ⟨j + 1, hj2⟩ = (lam.shape.rowLen (j + 1) : ℤ) :=
        (DominantWeight.natCast_rowLen_shape hlam ⟨j + 1, hj2⟩).symm
      have hcol : (lam.shape.rowLen (j + 1) : ℤ) +
          ∑ k ∈ Finset.range (i + 1), (T.1.rowCount (j + 1) k : ℤ) ≤
          (lam.shape.rowLen j : ℤ) + ∑ k ∈ Finset.range i, (T.1.rowCount j k : ℤ) := by
        exact_mod_cast T.1.rowLen_add_sum_range_rowCount_succ_le j i
      have hdiff1 :
          (∑ k ∈ Finset.range i, ∑ r ∈ Finset.range (j + 1), (T.1.rowCount r k : ℤ)) -
            (∑ k ∈ Finset.range i, ∑ r ∈ Finset.range j, (T.1.rowCount r k : ℤ)) =
          ∑ k ∈ Finset.range i, (T.1.rowCount j k : ℤ) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_range_succ]; abel
      have hdiff2 :
          (∑ k ∈ Finset.range (i + 1), ∑ r ∈ Finset.range (j + 2), (T.1.rowCount r k : ℤ)) -
            (∑ k ∈ Finset.range (i + 1), ∑ r ∈ Finset.range (j + 1), (T.1.rowCount r k : ℤ)) =
          ∑ k ∈ Finset.range (i + 1), (T.1.rowCount (j + 1) k : ℤ) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_range_succ]; abel
      linarith
    · intro i j hij hj
      simp only [lrHiveFun_productVertex, Finset.sum_range_succ (n := i + 1),
        Finset.sum_range_succ (n := i)]
      have hlat : ∑ r ∈ Finset.range (j + 1), (T.1.rowCount r (i + 1) : ℤ) ≤
          ∑ r ∈ Finset.range j, (T.1.rowCount r i : ℤ) := by
        exact_mod_cast (T.1.isLatticeWord_readingWord_iff.mp T.2.2) i j
      linarith

@[simp] theorem hiveOfLRTableau_apply {n : ℕ} {outer μ : YoungDiagram} {lam : DominantWeight n}
    (hlam : lam.IsPolynomial) (T : LRTableau lam.shape outer μ) (p : Vertex n) :
    hiveOfLRTableau hlam T p = lrHiveFun lam T.1 p := (rfl)

theorem hiveOfLRTableau_productVertex {n i j : ℕ} {outer μ : YoungDiagram}
    {lam : DominantWeight n} (hlam : lam.IsPolynomial) (T : LRTableau lam.shape outer μ)
    (hij : i ≤ j) (hj : j ≤ n) :
    hiveOfLRTableau hlam T (Vertex.productVertex n i j hij hj) =
      (∑ r : Fin n with r.val < j, lam.1 r) +
        ∑ k ∈ Finset.range i, ∑ r ∈ Finset.range j, (T.1.rowCount r k : ℤ) :=
  lrHiveFun_productVertex lam T.1 hij hj

/-- Along the diagonal `i = j`, `hiveOfLRTableau` records the prefix sums of `γ`. -/
theorem hiveOfLRTableau_productVertex_diag {n j : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) (hj : j ≤ n) :
    hiveOfLRTableau hlam T (Vertex.productVertex n j j le_rfl hj) =
      ∑ r : Fin n with r.val < j, γ.1 r := by
  rw [hiveOfLRTableau_productVertex, sum_filter_lt_eq_sum_range_rowLen hlam hj,
    sum_filter_lt_eq_sum_range_rowLen hγ hj, Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrj : r < j := Finset.mem_range.mp hr
  have hsum_nat : ∑ k ∈ Finset.range j, T.1.rowCount r k =
      γ.shape.rowLen r - lam.shape.rowLen r :=
    T.1.sum_range_rowCount_of_forall_lt fun c _ _ => (T.entry_le r c).trans_lt hrj
  have hle_row : lam.shape.rowLen r ≤ γ.shape.rowLen r :=
    YoungDiagram.rowLen_le_of_le T.1.le r
  rw [← Nat.cast_sum, hsum_nat]
  omega

/-- The clockwise cyclic boundary of `hiveOfLRTableau hlam T` is `productBoundary lam μ γ`. -/
@[simp] theorem boundary_hiveOfLRTableau {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) :
    (hiveOfLRTableau hlam T).boundary = productBoundary lam μ γ := by
  ext s m
  rw [boundary_apply]
  fin_cases s
  · dsimp only; simp only [Fin.zero_eta]
    have hsucc : Vertex.edgePoint n 0 m.succ =
        Vertex.productVertex n 0 (m.val + 1) (Nat.zero_le _) (by omega) :=
      (Vertex.productVertex_zero_left n (m.val + 1) (by omega)).symm
    have hcast : Vertex.edgePoint n 0 m.castSucc =
        Vertex.productVertex n 0 m.val (Nat.zero_le _) (by omega) :=
      (Vertex.productVertex_zero_left n m.val (by omega)).symm
    rw [hsucc, hcast, hiveOfLRTableau_productVertex, hiveOfLRTableau_productVertex,
      sum_filter_val_lt_succ m.isLt lam.1]
    simp
  · dsimp only; simp only [Fin.mk_one]
    have hsucc : Vertex.edgePoint n 1 m.succ =
        Vertex.productVertex n (m.val + 1) n (by omega) le_rfl :=
      (Vertex.productVertex_right_self n (m.val + 1) (by omega)).symm
    have hcast : Vertex.edgePoint n 1 m.castSucc =
        Vertex.productVertex n m.val n (by omega) le_rfl :=
      (Vertex.productVertex_right_self n m.val (by omega)).symm
    rw [hsucc, hcast, hiveOfLRTableau_productVertex, hiveOfLRTableau_productVertex,
      Finset.sum_range_succ]
    have hcont : ∑ r ∈ Finset.range n, T.1.rowCount r m.val = μ.shape.rowLen m.val := by
      rw [T.1.sum_range_rowCount_eq_content m.val (DominantWeight.colLen_zero_shape_le γ),
        congrFun T.2.1 m.val]
    have hμ_m : (μ.shape.rowLen m.val : ℤ) = μ.1 m := DominantWeight.natCast_rowLen_shape hμ m
    rw [← Nat.cast_sum, hcont, hμ_m]
    simp only [productBoundary_one]
    abel
  · dsimp only; simp only [Fin.reduceFinMk]
    have hsucc : Vertex.edgePoint n 2 m.succ =
        Vertex.productVertex n (n - (m.val + 1)) (n - (m.val + 1)) le_rfl (by omega) := by
      rw [Vertex.productVertex_diag]
      congr 1; ext; simp; omega
    have hcast : Vertex.edgePoint n 2 m.castSucc =
        Vertex.productVertex n ((n - (m.val + 1)) + 1) ((n - (m.val + 1)) + 1)
          le_rfl (by omega) := by
      rw [Vertex.productVertex_diag]
      congr 1; ext; simp; omega
    rw [hsucc, hcast, hiveOfLRTableau_productVertex_diag hlam hγ T,
      hiveOfLRTableau_productVertex_diag hlam hγ T,
      sum_filter_val_lt_succ (by omega : n - (m.val + 1) < n) γ.1]
    have hrev : (⟨n - (m.val + 1), by omega⟩ : Fin n) = m.rev := by ext; simp [Fin.val_rev]
    rw [hrev]
    simp only [productBoundary_two, DominantWeight.dual_apply]
    abel

/-- Bundled forward map into `FixedIntegerHive (productBoundary lam μ γ)`. -/
def fixedIntegerHiveOfLRTableau {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) :
    FixedIntegerHive (productBoundary lam μ γ) :=
  ⟨hiveOfLRTableau hlam T, boundary_hiveOfLRTableau hlam hμ hγ T⟩

@[simp] theorem coe_fixedIntegerHiveOfLRTableau {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) :
    (fixedIntegerHiveOfLRTableau hlam hμ hγ T).1 = hiveOfLRTableau hlam T := (rfl)

end ForwardMap

/-! ### Inverse map: row-count extraction and tableau reconstruction from a hive -/

section InverseMap

/-- Signed row-letter count extracted from a hive `h` at skew row `r` and letter `k`:
the mixed second difference off the diagonal (`k < r < n`), the single horizontal step on the
diagonal (`k = r < n`), and `0` elsewhere. -/
def hiveRowCountInt {n : ℕ} (h : Hive n ℤ) (r k : ℕ) : ℤ :=
  if hr : r < n then
    if hkr : k < r then
      h (Vertex.productVertex n (k + 1) (r + 1) (by omega) (by omega)) -
        h (Vertex.productVertex n k (r + 1) (by omega) (by omega)) -
        h (Vertex.productVertex n (k + 1) r (by omega) (by omega)) +
        h (Vertex.productVertex n k r (by omega) (by omega))
    else if k = r then
      h (Vertex.productVertex n (r + 1) (r + 1) le_rfl (by omega)) -
        h (Vertex.productVertex n r (r + 1) (by omega) (by omega))
    else 0
  else 0

theorem hiveRowCountInt_of_lt {n r k : ℕ} (h : Hive n ℤ) (hkr : k < r) (hr : r < n) :
    hiveRowCountInt h r k =
      h (Vertex.productVertex n (k + 1) (r + 1) (by omega) (by omega)) -
        h (Vertex.productVertex n k (r + 1) (by omega) (by omega)) -
        h (Vertex.productVertex n (k + 1) r (by omega) (by omega)) +
        h (Vertex.productVertex n k r (by omega) (by omega)) := by
  simp [hiveRowCountInt, hr, hkr]

theorem hiveRowCountInt_diag {n r : ℕ} (h : Hive n ℤ) (hr : r < n) :
    hiveRowCountInt h r r =
      h (Vertex.productVertex n (r + 1) (r + 1) le_rfl (by omega)) -
        h (Vertex.productVertex n r (r + 1) (by omega) (by omega)) := by
  simp [hiveRowCountInt, hr]

theorem hiveRowCountInt_eq_zero_of_lt {n r k : ℕ} (h : Hive n ℤ) (hrk : r < k) :
    hiveRowCountInt h r k = 0 := by
  by_cases hr : r < n
  · have h1 : ¬ k < r := by omega
    have h2 : k ≠ r := by omega
    simp [hiveRowCountInt, hr, h1, h2]
  · simp [hiveRowCountInt, hr]

theorem hiveRowCountInt_eq_zero_of_le {n r k : ℕ} (h : Hive n ℤ) (hnr : n ≤ r) :
    hiveRowCountInt h r k = 0 := by
  have hr : ¬ r < n := by omega
  simp [hiveRowCountInt, hr]

/-- **Column telescoping of `hiveRowCountInt`**: summing letter `k` across rows `r < x` (`x ≤ n`)
gives `h(k + 1, x) - h(k, x)` when `k < x`, and `0` when `x ≤ k`. -/
theorem sum_range_hiveRowCountInt_left {n x : ℕ} (h : Hive n ℤ) (k : ℕ) (hx : x ≤ n) :
    ∑ r ∈ Finset.range x, hiveRowCountInt h r k =
      if hkx : k < x then
        h (Vertex.productVertex n (k + 1) x hkx hx) -
          h (Vertex.productVertex n k x (Nat.le_of_lt hkx) hx)
      else 0 := by
  induction x with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    rcases lt_trichotomy k m with hkm | rfl | hmk
    · have hkm' : k < m + 1 := by omega
      rw [dite_eq_left hkm, dite_eq_left hkm', hiveRowCountInt_of_lt h hkm (by omega)]
      abel
    · rw [dite_eq_right (Nat.lt_irrefl k), dite_eq_left (Nat.lt_succ_self k), zero_add,
        hiveRowCountInt_diag h (by omega)]
    · have hnm : ¬ k < m := by omega
      have hnm' : ¬ k < m + 1 := by omega
      rw [dite_eq_right hnm, dite_eq_right hnm', hiveRowCountInt_eq_zero_of_lt h hmk, add_zero]

/-- **Double telescoping of `hiveRowCountInt`**: summing `hiveRowCountInt h r k` over `k < i` and
`r < j` (`0 ≤ i ≤ j ≤ n`) recovers `h(i, j) - h(0, j)`. -/
theorem sum_range_sum_range_hiveRowCountInt {n i j : ℕ} (h : Hive n ℤ)
    (hij : i ≤ j) (hj : j ≤ n) :
    ∑ k ∈ Finset.range i, ∑ r ∈ Finset.range j, hiveRowCountInt h r k =
      h (Vertex.productVertex n i j hij hj) -
        h (Vertex.productVertex n 0 j (Nat.zero_le j) hj) := by
  induction i with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega), sum_range_hiveRowCountInt_left h m hj,
      dite_eq_left (by omega : m < j)]
    abel

/-- Row-prefix telescoping for `i ≤ r < n`. -/
theorem sum_range_hiveRowCountInt_right {n i r : ℕ} (h : Hive n ℤ) (hir : i ≤ r) (hr : r < n) :
    ∑ k ∈ Finset.range i, hiveRowCountInt h r k =
      (h (Vertex.productVertex n i (r + 1) (by omega) (by omega)) -
          h (Vertex.productVertex n i r hir (by omega))) -
        (h (Vertex.productVertex n 0 (r + 1) (Nat.zero_le _) (by omega)) -
          h (Vertex.productVertex n 0 r (Nat.zero_le _) (by omega))) := by
  have h1 := sum_range_sum_range_hiveRowCountInt h (i := i) (j := r + 1) (by omega) (by omega)
  have h2 := sum_range_sum_range_hiveRowCountInt h (i := i) (j := r) hir (by omega)
  have hdiff :
      (∑ k ∈ Finset.range i, ∑ s ∈ Finset.range (r + 1), hiveRowCountInt h s k) -
        (∑ k ∈ Finset.range i, ∑ s ∈ Finset.range r, hiveRowCountInt h s k) =
      ∑ k ∈ Finset.range i, hiveRowCountInt h r k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_range_succ]; abel
  linarith

/-- Full-row telescoping across `k < m` (`r + 1 ≤ m`) for `r < n`. -/
theorem sum_range_hiveRowCountInt_full {n r m : ℕ} (h : Hive n ℤ) (hr : r < n) (hrm : r + 1 ≤ m) :
    ∑ k ∈ Finset.range m, hiveRowCountInt h r k =
      (h (Vertex.productVertex n (r + 1) (r + 1) le_rfl (by omega)) -
          h (Vertex.productVertex n r r le_rfl (by omega))) -
        (h (Vertex.productVertex n 0 (r + 1) (Nat.zero_le _) (by omega)) -
          h (Vertex.productVertex n 0 r (Nat.zero_le _) (by omega))) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrm
  have htail : ∑ x ∈ Finset.range d, hiveRowCountInt h r (r + 1 + x) = 0 :=
    Finset.sum_eq_zero fun x _ => hiveRowCountInt_eq_zero_of_lt h (by omega)
  rw [Finset.sum_range_add, htail, add_zero, Finset.sum_range_succ,
    sum_range_hiveRowCountInt_right h le_rfl hr, hiveRowCountInt_diag h hr]
  abel

/-- On any integer hive, the diagonal counts `hiveRowCountInt h r r` decrease weakly in `r < n`. -/
theorem hiveRowCountInt_diag_anti {n r₁ r₂ : ℕ} (h : Hive n ℤ)
    (hr₁₂ : r₁ ≤ r₂) (hr₂ : r₂ < n) :
    hiveRowCountInt h r₂ r₂ ≤ hiveRowCountInt h r₁ r₁ := by
  induction r₂, hr₁₂ using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih =>
    refine le_trans ?_ (ih (by omega))
    have hbal := h.le_of_isRhombus
      (isRhombus_productVertex_ballot (n := n) (i := m) (j := m + 1) (Nat.lt_succ_self m)
        (by omega))
    rw [hiveRowCountInt_diag h hr₂, hiveRowCountInt_diag h (by omega)]
    linarith

/-- **Nonnegativity of all extracted counts (including the diagonal)** when `μ` is polynomial. -/
theorem hiveRowCountInt_nonneg {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hμ : μ.IsPolynomial) (r k : ℕ) :
    0 ≤ hiveRowCountInt h r k := by
  by_cases hr : r < n
  · rcases lt_trichotomy k r with hkr | rfl | hrk
    · have hmix := h.le_of_isRhombus (isRhombus_productVertex_mixed hkr (by omega))
      rw [hiveRowCountInt_of_lt h hkr hr]
      linarith
    · have hn : 0 < n := by omega
      refine le_trans ?_ (hiveRowCountInt_diag_anti h (r₁ := k) (r₂ := n - 1)
        (by omega) (by omega))
      rw [hiveRowCountInt_diag h (by omega : n - 1 < n)]
      have hdiag : h (Vertex.productVertex n (n - 1 + 1) (n - 1 + 1) le_rfl (by omega)) =
          (∑ i, lam.1 i) + ∑ i, μ.1 i := by
        have hv : Vertex.productVertex n (n - 1 + 1) (n - 1 + 1) le_rfl (by omega) =
            Vertex.productVertex n n n le_rfl le_rfl := by ext <;> simp <;> omega
        have huniv : ({i : Fin n | i.val < n} : Finset (Fin n)) = Finset.univ := by ext i; simp
        rw [hv, apply_productVertex_diag_of_productBoundary hb le_rfl, huniv,
          ← sum_eq_of_productBoundary hb]
      have hside : h (Vertex.productVertex n (n - 1) (n - 1 + 1) (by omega) (by omega)) =
          (∑ i, lam.1 i) + ∑ i : Fin n with i.val < n - 1, μ.1 i := by
        have hv : Vertex.productVertex n (n - 1) (n - 1 + 1) (by omega) (by omega) =
            Vertex.productVertex n (n - 1) n (by omega) le_rfl := by ext <;> simp <;> omega
        rw [hv, apply_productVertex_right_self_of_productBoundary hb (by omega)]
      have hsum_μ : ∑ i : Fin n, μ.1 i =
          (∑ i : Fin n with i.val < n - 1, μ.1 i) + μ.1 ⟨n - 1, by omega⟩ := by
        have hall : ({i : Fin n | i.val < n - 1 + 1} : Finset (Fin n)) = Finset.univ := by
          ext i; simp; omega
        have hstep := sum_filter_val_lt_succ (by omega : n - 1 < n) μ.1
        rwa [hall] at hstep
      have hμ_nn : 0 ≤ μ.1 ⟨n - 1, by omega⟩ :=
        (DominantWeight.isPolynomial_def μ).mp hμ ⟨n - 1, by omega⟩
      linarith
    · rw [hiveRowCountInt_eq_zero_of_lt h hrk]
  · rw [hiveRowCountInt_eq_zero_of_le h (Nat.le_of_not_lt hr)]

/-- Natural-number row-letter count `a(r, k)` extracted from an integer hive `h`. -/
def hiveRowCount {n : ℕ} (h : IntegerHive n) (r k : ℕ) : ℕ :=
  (hiveRowCountInt h r k).toNat

theorem hiveRowCount_def {n : ℕ} (h : IntegerHive n) (r k : ℕ) :
    hiveRowCount h r k = (hiveRowCountInt h r k).toNat := (rfl)

theorem natCast_hiveRowCount {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hμ : μ.IsPolynomial) (r k : ℕ) :
    (hiveRowCount h r k : ℤ) = hiveRowCountInt h r k :=
  Int.toNat_of_nonneg (hiveRowCountInt_nonneg hb hμ r k)

theorem hiveRowCount_eq_zero_of_lt {n r k : ℕ} (h : IntegerHive n) (hrk : r < k) :
    hiveRowCount h r k = 0 := by
  simp [hiveRowCount, hiveRowCountInt_eq_zero_of_lt h hrk]

theorem hiveRowCount_eq_zero_of_le {n r k : ℕ} (h : IntegerHive n) (hnr : n ≤ r) :
    hiveRowCount h r k = 0 := by
  simp [hiveRowCount, hiveRowCountInt_eq_zero_of_le h hnr]

private theorem hiveRowCount_eq_zero_of_le_letter {n r k : ℕ} (h : IntegerHive n)
    (hnk : n ≤ k) : hiveRowCount h r k = 0 := by
  by_cases hr : r < n
  · exact hiveRowCount_eq_zero_of_lt h (lt_of_lt_of_le hr hnk)
  · exact hiveRowCount_eq_zero_of_le h (Nat.le_of_not_lt hr)

private theorem sum_range_hiveRowCount_of_le {n m : ℕ} (h : IntegerHive n) (k : ℕ)
    (hm : n ≤ m) :
    ∑ r ∈ Finset.range m, hiveRowCount h r k = ∑ r ∈ Finset.range n, hiveRowCount h r k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have htail : ∑ r ∈ Finset.range d, hiveRowCount h (n + r) k = 0 :=
    Finset.sum_eq_zero fun r _ => hiveRowCount_eq_zero_of_le h (by omega)
  rw [Finset.sum_range_add, htail, add_zero]

/-- Extracting `hiveRowCount` from `hiveOfLRTableau hlam T` recovers `T.1.rowCount` whenever
`outer.colLen 0 ≤ n`. -/
@[simp] theorem hiveRowCount_hiveOfLRTableau {n : ℕ} {outer μ : YoungDiagram}
    {lam : DominantWeight n} (hlam : lam.IsPolynomial) (houter : outer.colLen 0 ≤ n)
    (T : LRTableau lam.shape outer μ) (r k : ℕ) :
    hiveRowCount (hiveOfLRTableau hlam T) r k = T.1.rowCount r k := by
  by_cases hr : r < n
  · rcases lt_trichotomy k r with hkr | rfl | hrk
    · have hval : hiveRowCountInt (hiveOfLRTableau hlam T) r k = (T.1.rowCount r k : ℤ) := by
        rw [hiveRowCountInt_of_lt _ hkr hr]
        simp only [hiveOfLRTableau_productVertex, sum_filter_val_lt_succ hr lam.1,
          Finset.sum_range_succ]
        abel
      rw [hiveRowCount, hval, Int.toNat_natCast]
    · have hval : hiveRowCountInt (hiveOfLRTableau hlam T) k k = (T.1.rowCount k k : ℤ) := by
        rw [hiveRowCountInt_diag _ hr]
        simp only [hiveOfLRTableau_productVertex, Finset.sum_range_succ (n := k)]
        have hzero : ∑ s ∈ Finset.range k, (T.1.rowCount s k : ℤ) = 0 :=
          Finset.sum_eq_zero fun s hs => by simp [T.rowCount_eq_zero_of_lt (Finset.mem_range.mp hs)]
        linarith
      rw [hiveRowCount, hval, Int.toNat_natCast]
    · rw [hiveRowCount_eq_zero_of_lt _ hrk, T.rowCount_eq_zero_of_lt hrk]
  · have hnr : n ≤ r := Nat.le_of_not_lt hr
    rw [hiveRowCount_eq_zero_of_le _ hnr]
    have hlen : outer.rowLen r = 0 := YoungDiagram.rowLen_eq_zero_of_colLen_le (houter.trans hnr)
    simp [SkewSemistandardYoungTableau.rowCount_def, hlen]

private theorem shape_le_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ)
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial) :
    lam.shape ≤ γ.shape := by
  refine YoungDiagram.le_of_forall_rowLen_le fun r => ?_
  by_cases hr : r < n
  · have hfull := sum_range_hiveRowCountInt_full h hr le_rfl
    rw [apply_productVertex_diag_of_productBoundary hb (by omega),
      apply_productVertex_diag_of_productBoundary hb (by omega),
      apply_productVertex_zero_left_of_productBoundary hb (by omega),
      apply_productVertex_zero_left_of_productBoundary hb (by omega),
      sum_filter_val_lt_succ hr γ.1, sum_filter_val_lt_succ hr lam.1] at hfull
    have hnn : 0 ≤ ∑ k ∈ Finset.range (r + 1), hiveRowCountInt h r k :=
      Finset.sum_nonneg fun k _ => hiveRowCountInt_nonneg hb hμ r k
    have hle_int : lam.1 ⟨r, hr⟩ ≤ γ.1 ⟨r, hr⟩ := by linarith
    rw [← DominantWeight.natCast_rowLen_shape hlam ⟨r, hr⟩,
      ← DominantWeight.natCast_rowLen_shape hγ ⟨r, hr⟩] at hle_int
    exact Int.ofNat_le.mp hle_int
  · rw [DominantWeight.rowLen_shape_eq_zero_of_le _ (Nat.le_of_not_lt hr)]
    exact Nat.zero_le _

private theorem natCast_sum_hiveRowCount {n : ℕ} {α : Type*} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) (hμ : μ.IsPolynomial)
    (s : Finset α) (r k : α → ℕ) :
    ((∑ x ∈ s, hiveRowCount h (r x) (k x) : ℕ) : ℤ) =
      ∑ x ∈ s, hiveRowCountInt h (r x) (k x) := by
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl fun x _ => natCast_hiveRowCount hb hμ (r x) (k x)

private theorem sum_range_hiveRowCount_eq_rowLen_sub {n : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ)
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    {r m : ℕ} (hrm : r < m ∨ n ≤ m) :
    ∑ k ∈ Finset.range m, hiveRowCount h r k = γ.shape.rowLen r - lam.shape.rowLen r := by
  by_cases hr : r < n
  · have hcast := natCast_sum_hiveRowCount hb hμ (Finset.range m) (fun _ => r) (fun k => k)
    have hfull := sum_range_hiveRowCountInt_full (m := m) h hr (by omega)
    rw [apply_productVertex_diag_of_productBoundary hb (by omega),
      apply_productVertex_diag_of_productBoundary hb (by omega),
      apply_productVertex_zero_left_of_productBoundary hb (by omega),
      apply_productVertex_zero_left_of_productBoundary hb (by omega),
      sum_filter_val_lt_succ hr γ.1, sum_filter_val_lt_succ hr lam.1,
      ← DominantWeight.natCast_rowLen_shape hγ ⟨r, hr⟩,
      ← DominantWeight.natCast_rowLen_shape hlam ⟨r, hr⟩] at hfull
    have hle := YoungDiagram.rowLen_le_of_le (shape_le_of_productBoundary hb hlam hμ hγ) r
    exact Int.ofNat_inj.mp (by rw [Nat.cast_sub hle, hcast]; linarith)
  · have hnr : n ≤ r := Nat.le_of_not_lt hr
    rw [Finset.sum_eq_zero fun k _ => hiveRowCount_eq_zero_of_le h hnr,
      DominantWeight.rowLen_shape_eq_zero_of_le _ hnr,
      DominantWeight.rowLen_shape_eq_zero_of_le _ hnr]
    rfl

private theorem sum_hiveRowCount_eq_rowLen_sub {n : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ)
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial) (r : ℕ) :
    ∑ k ∈ Finset.range n, hiveRowCount h r k = γ.shape.rowLen r - lam.shape.rowLen r :=
  sum_range_hiveRowCount_eq_rowLen_sub hb hlam hμ hγ (Or.inr le_rfl)

private theorem col_strict_hiveRowCount {n : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ)
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial) (r x : ℕ) :
    lam.shape.rowLen (r + 1) + ∑ k ∈ Finset.range (x + 1), hiveRowCount h (r + 1) k ≤
      lam.shape.rowLen r + ∑ k ∈ Finset.range x, hiveRowCount h r k := by
  by_cases hr1 : r + 1 < n
  · have hr : r < n := by omega
    by_cases hxr : x ≤ r
    · have hcol_rh := h.le_of_isRhombus (isRhombus_productVertex_col hxr (by omega : r + 2 ≤ n))
      have hs1 := sum_range_hiveRowCountInt_right h (i := x + 1) (r := r + 1) (by omega) hr1
      have hs0 := sum_range_hiveRowCountInt_right h (i := x) (r := r) hxr hr
      rw [apply_productVertex_zero_left_of_productBoundary hb (by omega),
        apply_productVertex_zero_left_of_productBoundary hb (by omega),
        sum_filter_val_lt_succ hr1 lam.1,
        ← DominantWeight.natCast_rowLen_shape hlam ⟨r + 1, hr1⟩] at hs1
      rw [apply_productVertex_zero_left_of_productBoundary hb (by omega),
        apply_productVertex_zero_left_of_productBoundary hb (by omega),
        sum_filter_val_lt_succ hr lam.1,
        ← DominantWeight.natCast_rowLen_shape hlam ⟨r, hr⟩] at hs0
      have hc1 :=
        natCast_sum_hiveRowCount hb hμ (Finset.range (x + 1)) (fun _ => r + 1) (fun k => k)
      have hc0 := natCast_sum_hiveRowCount hb hμ (Finset.range x) (fun _ => r) (fun k => k)
      exact Int.ofNat_le.mp (by rw [Nat.cast_add, Nat.cast_add, hc1, hc0]; linarith)
    · rw [sum_range_hiveRowCount_eq_rowLen_sub hb hlam hμ hγ (Or.inl (by omega)),
        sum_range_hiveRowCount_eq_rowLen_sub hb hlam hμ hγ (Or.inl (by omega))]
      have hle1 :=
        YoungDiagram.rowLen_le_of_le (shape_le_of_productBoundary hb hlam hμ hγ) (r + 1)
      have hle0 := YoungDiagram.rowLen_le_of_le (shape_le_of_productBoundary hb hlam hμ hγ) r
      have hanti := γ.shape.rowLen_anti r (r + 1) (Nat.le_succ r)
      omega
  · have hnr : n ≤ r + 1 := Nat.le_of_not_lt hr1
    rw [DominantWeight.rowLen_shape_eq_zero_of_le _ hnr,
      Finset.sum_eq_zero fun k _ => hiveRowCount_eq_zero_of_le h hnr, zero_add]
    exact Nat.zero_le _

private theorem ballot_hiveRowCount {n : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) (hμ : μ.IsPolynomial)
    (k x : ℕ) :
    ∑ r ∈ Finset.range (x + 1), hiveRowCount h r (k + 1) ≤
      ∑ r ∈ Finset.range x, hiveRowCount h r k := by
  by_cases hk1 : k + 1 < n
  · by_cases hkx : k < x
    · rcases lt_or_ge x n with hxn | hnx
      · have hbal_rh := h.le_of_isRhombus (isRhombus_productVertex_ballot hkx (by omega))
        have hs1 := sum_range_hiveRowCountInt_left h (k + 1) (by omega : x + 1 ≤ n)
        have hs0 := sum_range_hiveRowCountInt_left h k (by omega : x ≤ n)
        rw [dite_eq_left (by omega : k + 1 < x + 1)] at hs1; rw [dite_eq_left hkx] at hs0
        have hc1 :=
          natCast_sum_hiveRowCount hb hμ (Finset.range (x + 1)) (fun r => r) (fun _ => k + 1)
        have hc0 := natCast_sum_hiveRowCount hb hμ (Finset.range x) (fun r => r) (fun _ => k)
        exact Int.ofNat_le.mp (by rw [hc1, hc0]; linarith)
      · rw [sum_range_hiveRowCount_of_le h (k + 1) (by omega),
          sum_range_hiveRowCount_of_le h k hnx]
        have hs1 := sum_range_hiveRowCountInt_left h (k + 1) le_rfl
        have hs0 := sum_range_hiveRowCountInt_left h k le_rfl
        rw [dite_eq_left hk1, apply_productVertex_right_self_of_productBoundary hb (by omega),
          apply_productVertex_right_self_of_productBoundary hb (by omega),
          sum_filter_val_lt_succ hk1 μ.1] at hs1
        rw [dite_eq_left (by omega : k < n),
          apply_productVertex_right_self_of_productBoundary hb (by omega),
          apply_productVertex_right_self_of_productBoundary hb (by omega),
          sum_filter_val_lt_succ (by omega : k < n) μ.1] at hs0
        have hc1 := natCast_sum_hiveRowCount hb hμ (Finset.range n) (fun r => r) (fun _ => k + 1)
        have hc0 := natCast_sum_hiveRowCount hb hμ (Finset.range n) (fun r => r) (fun _ => k)
        have hanti : μ.1 ⟨k + 1, hk1⟩ ≤ μ.1 ⟨k, by omega⟩ :=
          μ.antitone (Fin.mk_le_mk.mpr (Nat.le_succ k))
        exact Int.ofNat_le.mp (by rw [hc1, hc0]; linarith)
    · rw [Finset.sum_eq_zero fun r hr =>
        hiveRowCount_eq_zero_of_lt h (by have := Finset.mem_range.mp hr; omega)]
      exact Nat.zero_le _
  · rw [Finset.sum_eq_zero fun r _ =>
        hiveRowCount_eq_zero_of_le_letter h (Nat.le_of_not_lt hk1)]
    exact Nat.zero_le _

private def lrSkewTableauOfHive {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    SkewSemistandardYoungTableau lam.shape γ.shape :=
  SkewSemistandardYoungTableau.ofRowCount
    (shape_le_of_productBoundary h.2 hlam hμ hγ) n (hiveRowCount h.1)
    (sum_hiveRowCount_eq_rowLen_sub h.2 hlam hμ hγ)
    (col_strict_hiveRowCount h.2 hlam hμ hγ)

private theorem rowCount_lrSkewTableauOfHive {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r k : ℕ) :
    (lrSkewTableauOfHive hlam hμ hγ h).rowCount r k = hiveRowCount h.1 r k :=
  SkewSemistandardYoungTableau.rowCount_ofRowCount
    (shape_le_of_productBoundary h.2 hlam hμ hγ)
    (sum_hiveRowCount_eq_rowLen_sub h.2 hlam hμ hγ)
    (col_strict_hiveRowCount h.2 hlam hμ hγ)
    (fun _ _ hnk => hiveRowCount_eq_zero_of_le_letter h.1 hnk) r k

/-- Reconstruct the Littlewood–Richardson tableau of shape `γ.shape / λ.shape` and content
`μ.shape` from an integer hive with boundary `productBoundary λ μ γ`. -/
def lrTableauOfHive {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    LRTableau lam.shape γ.shape μ.shape := by
  let S := lrSkewTableauOfHive hlam hμ hγ h
  have hrc := rowCount_lrSkewTableauOfHive hlam hμ hγ h
  refine ⟨S, funext fun k => ?_, ?_⟩
  · rw [← S.sum_range_rowCount_eq_content k (DominantWeight.colLen_zero_shape_le γ),
      Finset.sum_congr rfl fun r _ => hrc r k]
    by_cases hk : k < n
    · have hs := sum_range_hiveRowCountInt_left h.1 k le_rfl
      rw [dite_eq_left hk, apply_productVertex_right_self_of_productBoundary h.2 (by omega),
        apply_productVertex_right_self_of_productBoundary h.2 (by omega),
        sum_filter_val_lt_succ hk μ.1, ← DominantWeight.natCast_rowLen_shape hμ ⟨k, hk⟩] at hs
      have hc := natCast_sum_hiveRowCount h.2 hμ (Finset.range n) (fun r => r) (fun _ => k)
      exact Int.ofNat_inj.mp (by rw [hc]; linarith)
    · rw [DominantWeight.rowLen_shape_eq_zero_of_le μ (Nat.le_of_not_lt hk)]
      exact Finset.sum_eq_zero fun _ _ =>
        hiveRowCount_eq_zero_of_le_letter h.1 (Nat.le_of_not_lt hk)
  · rw [S.isLatticeWord_readingWord_iff]
    intro k x
    simp only [S, hrc]
    exact ballot_hiveRowCount h.2 hμ k x

@[simp] theorem rowCount_lrTableauOfHive {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r k : ℕ) :
    (lrTableauOfHive hlam hμ hγ h).1.rowCount r k = hiveRowCount h.1 r k :=
  rowCount_lrSkewTableauOfHive hlam hμ hγ h r k

/-- **The hive-to-Littlewood–Richardson equivalence** for polynomial dominant weights `λ, μ, γ`:
an explicit bijection between normalized integer hives with clockwise boundary `(λ, μ, γ*)` and
Littlewood–Richardson tableaux of shape `γ.shape / λ.shape` and content `μ.shape`. -/
def fixedIntegerHiveEquivLRTableau {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial) :
    FixedIntegerHive (productBoundary lam μ γ) ≃ LRTableau lam.shape γ.shape μ.shape where
  toFun := lrTableauOfHive hlam hμ hγ
  invFun := fixedIntegerHiveOfLRTableau hlam hμ hγ
  left_inv h := by
    apply Subtype.ext; ext p
    rw [← Vertex.productVertex_z_add p, coe_fixedIntegerHiveOfLRTableau,
      hiveOfLRTableau_productVertex]
    simp only [rowCount_lrTableauOfHive, natCast_hiveRowCount h.2 hμ]
    rw [sum_range_sum_range_hiveRowCountInt h.1 (Nat.le_add_left _ _)
        (by have := p.sum_eq; omega),
      apply_productVertex_zero_left_of_productBoundary h.2 (by have := p.sum_eq; omega)]
    abel
  right_inv T := by
    apply Subtype.ext
    refine SkewSemistandardYoungTableau.eq_of_rowCount_eq fun r k => ?_
    rw [rowCount_lrTableauOfHive, coe_fixedIntegerHiveOfLRTableau,
      hiveRowCount_hiveOfLRTableau hlam (DominantWeight.colLen_zero_shape_le γ) T]

@[simp] theorem fixedIntegerHiveEquivLRTableau_apply {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    fixedIntegerHiveEquivLRTableau hlam hμ hγ h = lrTableauOfHive hlam hμ hγ h := (rfl)

@[simp] theorem fixedIntegerHiveEquivLRTableau_symm_apply {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) :
    (fixedIntegerHiveEquivLRTableau hlam hμ hγ).symm T =
      fixedIntegerHiveOfLRTableau hlam hμ hγ T := (rfl)

/-- Young-diagram form of the hive-to-LR equivalence on `weightOfShape n` for diagrams of at most
`n` rows. -/
def fixedIntegerHiveWeightOfShapeEquivLRTableau {n : ℕ} {lam μ ν : YoungDiagram}
    (hlam : lam.colLen 0 ≤ n) (hμ : μ.colLen 0 ≤ n) (hν : ν.colLen 0 ≤ n) :
    FixedIntegerHive
      (productBoundary (weightOfShape n lam) (weightOfShape n μ) (weightOfShape n ν)) ≃
      LRTableau lam ν μ :=
  (fixedIntegerHiveEquivLRTableau (isPolynomial_weightOfShape n lam)
    (isPolynomial_weightOfShape n μ) (isPolynomial_weightOfShape n ν)).trans
    (LRTableau.congr (shape_weightOfShape hlam) (shape_weightOfShape hν)
      (shape_weightOfShape hμ))

/-- The row-letter counts of `fixedIntegerHiveWeightOfShapeEquivLRTableau hlam hμ hν h` agree with
`hiveRowCount h.1`. -/
@[simp] theorem rowCount_fixedIntegerHiveWeightOfShapeEquivLRTableau
    {n : ℕ} {lam μ ν : YoungDiagram}
    (hlam : lam.colLen 0 ≤ n) (hμ : μ.colLen 0 ≤ n) (hν : ν.colLen 0 ≤ n)
    (h : FixedIntegerHive
      (productBoundary (weightOfShape n lam) (weightOfShape n μ) (weightOfShape n ν)))
    (r k : ℕ) :
    (fixedIntegerHiveWeightOfShapeEquivLRTableau hlam hμ hν h).1.rowCount r k =
      hiveRowCount h.1 r k := by
  simp [fixedIntegerHiveWeightOfShapeEquivLRTableau]

/-- Evaluating the inverse of `fixedIntegerHiveWeightOfShapeEquivLRTableau` at `p : Vertex n` gives
`lrHiveFun (weightOfShape n lam) T.1 p`. -/
@[simp] theorem coe_fixedIntegerHiveWeightOfShapeEquivLRTableau_symm_apply
    {n : ℕ} {lam μ ν : YoungDiagram}
    (hlam : lam.colLen 0 ≤ n) (hμ : μ.colLen 0 ≤ n) (hν : ν.colLen 0 ≤ n)
    (T : LRTableau lam ν μ) (p : Vertex n) :
    ((fixedIntegerHiveWeightOfShapeEquivLRTableau hlam hμ hν).symm T).1 p =
      lrHiveFun (weightOfShape n lam) T.1 p := by
  simp [fixedIntegerHiveWeightOfShapeEquivLRTableau, lrHiveFun]

end InverseMap

/-! ### Affine determinant shifts and arbitrary signed dominant weights -/

section DeterminantShift

private theorem isPolynomial_shift_neg_add_detShift {n : ℕ} {lam μ γ : DominantWeight n}
    (hdet : lam.detShift + μ.detShift ≤ γ.detShift) :
    (γ.shift (-lam.detShift + -μ.detShift)).IsPolynomial := by
  rw [DominantWeight.isPolynomial_iff_zero_le_detShift]
  cases n with
  | zero => simp
  | succ m =>
    rw [DominantWeight.detShift_shift]
    linarith [hdet]

private theorem shape_shift_neg_detShift {n : ℕ} (l : DominantWeight n) :
    (l.shift (-l.detShift)).shape = l.detShiftShape := by
  rw [← DominantWeight.weightOfShape_detShiftShape,
    shape_weightOfShape l.colLen_zero_detShiftShape_le]

/-- **Canonical signed hive-to-LR equivalence**: for arbitrary signed dominant weights `λ, μ, γ`
satisfying `λ.detShift + μ.detShift ≤ γ.detShift`, subtracting `λ.detShift` and `μ.detShift`
identifies `FixedIntegerHive (productBoundary λ μ γ)` with the Littlewood–Richardson tableaux of
shape `(γ.shift (-(λ.detShift + μ.detShift))).shape / λ.detShiftShape` and content
`μ.detShiftShape`. -/
def fixedIntegerHiveSignedEquivLRTableau {n : ℕ} {lam μ γ : DominantWeight n}
    (hdet : lam.detShift + μ.detShift ≤ γ.detShift) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      LRTableau lam.detShiftShape (γ.shift (-(lam.detShift + μ.detShift))).shape
        μ.detShiftShape :=
  (fixedIntegerHiveShiftEquiv lam μ γ (-lam.detShift) (-μ.detShift)).trans <|
    (fixedIntegerHiveEquivLRTableau
      (DominantWeight.isPolynomial_shift_neg_detShift lam)
      (DominantWeight.isPolynomial_shift_neg_detShift μ)
      (isPolynomial_shift_neg_add_detShift hdet)).trans
    (LRTableau.congr (shape_shift_neg_detShift lam)
      (congrArg (fun c => (γ.shift c).shape) (neg_add lam.detShift μ.detShift).symm)
      (shape_shift_neg_detShift μ))

/-- The row-letter counts of `fixedIntegerHiveSignedEquivLRTableau hdet h` equal `hiveRowCount` of
the determinant-shifted hive `h.1 + affine n (-lam.detShift) (-lam.detShift - μ.detShift)`. -/
@[simp] theorem rowCount_fixedIntegerHiveSignedEquivLRTableau
    {n : ℕ} {lam μ γ : DominantWeight n}
    (hdet : lam.detShift + μ.detShift ≤ γ.detShift)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r k : ℕ) :
    (fixedIntegerHiveSignedEquivLRTableau hdet h).1.rowCount r k =
      hiveRowCount (h.1 + affine n (-lam.detShift) (-lam.detShift - μ.detShift)) r k := by
  simp [fixedIntegerHiveSignedEquivLRTableau, sub_eq_add_neg]

/-- Evaluating the inverse of `fixedIntegerHiveSignedEquivLRTableau` at `p : Vertex n` adds
`affine n lam.detShift (lam.detShift + μ.detShift) p` to
`lrHiveFun (lam.shift (-lam.detShift)) T.1 p`. -/
@[simp] theorem coe_fixedIntegerHiveSignedEquivLRTableau_symm_apply
    {n : ℕ} {lam μ γ : DominantWeight n}
    (hdet : lam.detShift + μ.detShift ≤ γ.detShift)
    (T : LRTableau lam.detShiftShape (γ.shift (-(lam.detShift + μ.detShift))).shape
      μ.detShiftShape)
    (p : Vertex n) :
    ((fixedIntegerHiveSignedEquivLRTableau hdet).symm T).1 p =
      lrHiveFun (lam.shift (-lam.detShift)) T.1 p +
        affine n lam.detShift (lam.detShift + μ.detShift) p := by
  simp [fixedIntegerHiveSignedEquivLRTableau, lrHiveFun]

end DeterminantShift

/-! ### Concrete rank-`2` check -/

section Checks

/-- **Rank-`2` check (`λ = μ = (1, 0)`, `γ = (1, 1)`)**: `detTwo` corresponds under
`fixedIntegerHiveEquivLRTableau` to the unique LR tableau of shape `(1, 1) / (1)` and content
`(1)`, with `rowCount 1 0 = 1`, `detTwo(1, 1) = 1`, and `detTwo(1, 2) = 2`. -/
theorem rowCount_lrTableau_detTwo :
    let lam : DominantWeight 2 := ⟨![1, 0], by decide⟩
    let γ : DominantWeight 2 := ⟨![1, 1], by decide⟩
    let hlam : lam.IsPolynomial := by
      rw [DominantWeight.isPolynomial_iff_zero_le_detShift, DominantWeight.detShift_succ]; decide
    let hγ : γ.IsPolynomial := by
      rw [DominantWeight.isPolynomial_iff_zero_le_detShift, DominantWeight.detShift_succ]; decide
    let T := fixedIntegerHiveEquivLRTableau hlam hlam hγ ⟨detTwo, boundary_detTwo⟩
    T.1.rowCount 1 0 = 1 ∧
      detTwo (Vertex.productVertex 2 1 1 le_rfl (by decide)) = 1 ∧
      detTwo (Vertex.productVertex 2 1 2 (by decide) le_rfl) = 2 := by
  refine ⟨?_, by simp, by simp⟩
  rw [fixedIntegerHiveEquivLRTableau_apply, rowCount_lrTableauOfHive, hiveRowCount,
    hiveRowCountInt_of_lt _ (by decide) (by decide)]
  simp

end Checks

end TauCeti.Hive
