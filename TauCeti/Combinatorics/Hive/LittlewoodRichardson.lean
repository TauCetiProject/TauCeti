/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.Combinatorics.Hive.Fibre
public import TauCeti.Combinatorics.Young.LittlewoodRichardson.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic
import Mathlib.RepresentationTheory.FDRep
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import TauCeti.Combinatorics.Young.LittlewoodRichardson.Yamanouchi
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.LittlewoodRichardson
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Weight.HighestWeight
import TauCeti.RepresentationTheory.FDRep.Basic
import TauCeti.RepresentationTheory.Intertwining
import TauCeti.RepresentationTheory.Rep.DirectSum.Basic
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.LittlewoodRichardson

/-!
# The hive–Littlewood–Richardson equivalence and `GLₙ(ℂ)` tensor multiplicities

In the `(i, j)` product chart `Vertex.ofIJ n i j = (n - j, j - i, i)` (`0 ≤ i ≤ j ≤ n`), the
exhaustive three-family rhombus classification (`IsRhombus.cases_ofIJ`) characterizes rhombus
concavity by three families of inequalities (`isRhombusConcave_iff_ofIJ`): right-leaning,
left-leaning, and upright unit rhombi.

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
weights, giving both shift-independent bijections (`fixedIntegerHiveEquivLRTableauShift`,
`fixedIntegerHiveEquivLRTableauDetShift`) and the unconditional count
`hiveCount_productBoundary_eq_ite_natCard_lrTableau`.

Combining this bijection with the Littlewood–Richardson rules for Schur polynomials and rational
Weyl modules of `GLₙ(ℂ)` yields:

* **Schur-polynomial expansion** (`TauCeti.Hive.schur_mul_eq_finsum_hiveCount`): over any
  commutative semiring `R`, `s_λ · s_μ = ∑ᶠ γ, hiveCount (productBoundary λ μ γ) • s_γ`;
* **`GLₙ(ℂ)` tensor-product multiplicities** (`TauCeti.Hive.finrank_hom_eq_hiveCount`): for
  arbitrary dominant weights `λ, μ, γ`,
  `Module.finrank ℂ (V_γ ⟶ V_λ ⊗ V_μ) = hiveCount (productBoundary λ μ γ)`;
* **Commutativity** (`TauCeti.Hive.hiveCount_comm`):
  `hiveCount (productBoundary λ μ γ) = hiveCount (productBoundary μ λ γ)`.

## Main definitions

* `TauCeti.Hive.hiveOfLRTableau`, `TauCeti.Hive.lrTableauOfHive`: the two directions of the
  hive–Littlewood–Richardson dictionary on polynomial dominant weights.
* `TauCeti.Hive.fixedIntegerHiveEquivLRTableau`: explicit bijection between polynomial-boundary
  integer hives and Littlewood–Richardson tableaux.
* `TauCeti.Hive.fixedIntegerHiveEquivLRTableauShift`,
  `TauCeti.Hive.fixedIntegerHiveEquivLRTableauDetShift`: signed-weight bijections via affine
  determinant shifts.

## Main results

* `TauCeti.Hive.isRhombusConcave_iff_ofIJ`: three-family `(i, j)`-chart characterization of rhombus
  concavity.
* `TauCeti.Hive.hiveCount_productBoundary_eq_natCard_lrTableau`,
  `TauCeti.Hive.hiveCount_productBoundary_eq_ite_natCard_lrTableau`: hive counts equal
  Littlewood–Richardson coefficients for polynomial and arbitrary signed weights.
* `TauCeti.Hive.schur_mul_eq_finsum_hiveCount`: the hive Littlewood–Richardson rule for Schur
  polynomials over any commutative semiring.
* `TauCeti.Hive.finrank_hom_eq_hiveCount`: `GLₙ(ℂ)` rational tensor-product multiplicities equal
  `hiveCount`.
* `TauCeti.Hive.hiveCount_comm`: commutativity of `hiveCount` in the two input weights.

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
open CategoryTheory MonoidalCategory

namespace TauCeti.Hive

/-! ### Three-family `(i, j)`-chart characterization of rhombus concavity -/

section ChartConcavity

/-- **Three-family `(i, j)`-chart characterization of rhombus concavity**: a lattice function
`f : Vertex n → R` is rhombus-concave iff it satisfies the right-leaning, left-leaning, and
upright unit-rhombus inequalities in `(i, j)` coordinates. -/
theorem isRhombusConcave_iff_ofIJ {n : ℕ} {R : Type*} [AddCommGroup R] [Preorder R]
    (f : Vertex n → R) :
    IsRhombusConcave f ↔
      (∀ (i j : ℕ) (hij : i ≤ j) (hjn : j + 2 ≤ n),
        f (Vertex.ofIJ n i j hij (by omega)) +
            f (Vertex.ofIJ n (i + 1) (j + 2) (by omega) hjn) ≤
          f (Vertex.ofIJ n i (j + 1) (by omega) (by omega)) +
            f (Vertex.ofIJ n (i + 1) (j + 1) (by omega) (by omega))) ∧
      (∀ (i j : ℕ) (hij : i < j) (hjn : j + 1 ≤ n),
        f (Vertex.ofIJ n i j hij.le (by omega)) +
            f (Vertex.ofIJ n (i + 2) (j + 1) (by omega) hjn) ≤
          f (Vertex.ofIJ n (i + 1) j hij (by omega)) +
            f (Vertex.ofIJ n (i + 1) (j + 1) (by omega) hjn)) ∧
      (∀ (i j : ℕ) (hij : i < j) (hjn : j + 1 ≤ n),
        f (Vertex.ofIJ n (i + 1) j hij (by omega)) +
            f (Vertex.ofIJ n i (j + 1) (by omega) hjn) ≤
          f (Vertex.ofIJ n i j hij.le (by omega)) +
            f (Vertex.ofIJ n (i + 1) (j + 1) (by omega) hjn)) := by
  rw [isRhombusConcave_def]
  refine ⟨fun hf => ⟨fun i j hij hjn => hf (isRhombus_ofIJ_right hij hjn),
    fun i j hij hjn => hf (isRhombus_ofIJ_left hij hjn),
    fun i j hij hjn => hf (isRhombus_ofIJ_upright hij hjn)⟩, fun ⟨hr, hl, hu⟩ a b c d h => ?_⟩
  exact h.cases_ofIJ (P := fun a b c d => f b + f d ≤ f a + f c)
    (fun a _ c _ h' => by rwa [add_comm (f a) (f c)] at h')
    (fun _ b _ d h' => by rwa [add_comm (f b) (f d)] at h')
    hr hl hu

variable {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]

/-- Right-leaning `(i, j)`-chart rhombus inequality for a hive `h`. -/
theorem le_ofIJ_right (h : Hive n R) {i j : ℕ} (hij : i ≤ j) (hjn : j + 2 ≤ n) :
    h (Vertex.ofIJ n i j hij (by omega)) +
        h (Vertex.ofIJ n (i + 1) (j + 2) (by omega) hjn) ≤
      h (Vertex.ofIJ n i (j + 1) (by omega) (by omega)) +
        h (Vertex.ofIJ n (i + 1) (j + 1) (by omega) (by omega)) :=
  h.le_of_isRhombus (isRhombus_ofIJ_right hij hjn)

/-- Left-leaning `(i, j)`-chart rhombus inequality for a hive `h`. -/
theorem le_ofIJ_left (h : Hive n R) {i j : ℕ} (hij : i < j) (hjn : j + 1 ≤ n) :
    h (Vertex.ofIJ n i j hij.le (by omega)) +
        h (Vertex.ofIJ n (i + 2) (j + 1) (by omega) hjn) ≤
      h (Vertex.ofIJ n (i + 1) j hij (by omega)) +
        h (Vertex.ofIJ n (i + 1) (j + 1) (by omega) hjn) :=
  h.le_of_isRhombus (isRhombus_ofIJ_left hij hjn)

/-- Upright `(i, j)`-chart rhombus inequality for a hive `h`. -/
theorem le_ofIJ_upright (h : Hive n R) {i j : ℕ} (hij : i < j) (hjn : j + 1 ≤ n) :
    h (Vertex.ofIJ n (i + 1) j hij (by omega)) +
        h (Vertex.ofIJ n i (j + 1) (by omega) hjn) ≤
      h (Vertex.ofIJ n i j hij.le (by omega)) +
        h (Vertex.ofIJ n (i + 1) (j + 1) (by omega) hjn) :=
  h.le_of_isRhombus (isRhombus_ofIJ_upright hij hjn)

end ChartConcavity

/-! ### Forward map: Littlewood–Richardson tableaux to integer hives -/

section ForwardMap

/-- In a Littlewood–Richardson tableau, row `r` contains no letter strictly larger than `r`. -/
private theorem lrTableau_rowCount_eq_zero_of_lt {inner outer ν : YoungDiagram}
    (T : LRTableau inner outer ν) {r k : ℕ} (h : r < k) : T.1.rowCount r k = 0 := by
  rw [SkewSemistandardYoungTableau.rowCount_def, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _ hjk
  have := T.entry_le r j
  omega

variable {n : ℕ} {lam μ γ : DominantWeight n}

/-- Partial-sum lattice function associated to a Littlewood–Richardson tableau `T`. -/
private def lrHiveFun (T : LRTableau lam.shape γ.shape μ.shape) (p : Vertex n) : ℤ :=
  (∑ r ∈ Finset.range (p.y + p.z), (lam.shape.rowLen r : ℤ)) +
    ∑ k ∈ Finset.range p.z, ∑ r ∈ Finset.range (p.y + p.z), (T.1.rowCount r k : ℤ)

private theorem lrHiveFun_ofIJ (T : LRTableau lam.shape γ.shape μ.shape) {i j : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) :
    lrHiveFun T (Vertex.ofIJ n i j hij hjn) =
      (∑ r ∈ Finset.range j, (lam.shape.rowLen r : ℤ)) +
        ∑ k ∈ Finset.range i, ∑ r ∈ Finset.range j, (T.1.rowCount r k : ℤ) := by
  simp [lrHiveFun, Nat.sub_add_cancel hij]

private theorem lrHiveFun_step_j (T : LRTableau lam.shape γ.shape μ.shape) {i j : ℕ}
    (hij : i ≤ j) (hjn : j + 1 ≤ n) :
    lrHiveFun T (Vertex.ofIJ n i (j + 1) (by omega) hjn) -
        lrHiveFun T (Vertex.ofIJ n i j hij (by omega)) =
      (lam.shape.rowLen j : ℤ) + ∑ k ∈ Finset.range i, (T.1.rowCount j k : ℤ) := by
  rw [lrHiveFun_ofIJ, lrHiveFun_ofIJ, Finset.sum_range_succ]
  simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
  abel

private theorem lrHiveFun_step_i (T : LRTableau lam.shape γ.shape μ.shape) {i j : ℕ}
    (hij : i < j) (hjn : j ≤ n) :
    lrHiveFun T (Vertex.ofIJ n (i + 1) j hij hjn) -
        lrHiveFun T (Vertex.ofIJ n i j hij.le hjn) =
      ∑ r ∈ Finset.range j, (T.1.rowCount r i : ℤ) := by
  rw [lrHiveFun_ofIJ, lrHiveFun_ofIJ, Finset.sum_range_succ]
  abel

private theorem isRhombusConcave_lrHiveFun (T : LRTableau lam.shape γ.shape μ.shape) :
    IsRhombusConcave (lrHiveFun T) := by
  rw [isRhombusConcave_iff_ofIJ]
  refine ⟨fun i j hij hjn => ?_, fun i j hij hjn => ?_, fun i j hij hjn => ?_⟩
  · have h1 := lrHiveFun_step_j T (i := i + 1) (j := j + 1) (by omega) hjn
    have h2 := lrHiveFun_step_j T (i := i) (j := j) hij (by omega)
    have hcol : (lam.shape.rowLen (j + 1) : ℤ) +
        ∑ k ∈ Finset.range (i + 1), (T.1.rowCount (j + 1) k : ℤ) ≤
        (lam.shape.rowLen j : ℤ) + ∑ k ∈ Finset.range i, (T.1.rowCount j k : ℤ) := by
      exact_mod_cast T.1.rowLen_add_sum_range_rowCount_succ_le j i
    linarith
  · have h1 := lrHiveFun_step_i T (i := i + 1) (j := j + 1) (by omega) hjn
    have h2 := lrHiveFun_step_i T (i := i) (j := j) hij (by omega)
    have hlat : ∑ r ∈ Finset.range (j + 1), (T.1.rowCount r (i + 1) : ℤ) ≤
        ∑ r ∈ Finset.range j, (T.1.rowCount r i : ℤ) := by
      exact_mod_cast (T.1.isLatticeWord_readingWord_iff.mp T.2.2) i j
    linarith
  · have h1 := lrHiveFun_step_i T (i := i) (j := j + 1) (by omega) hjn
    have h2 := lrHiveFun_step_i T (i := i) (j := j) hij (by omega)
    rw [Finset.sum_range_succ] at h1
    linarith [Int.natCast_nonneg (T.1.rowCount j i)]

private theorem lrHiveFun_step_diag (T : LRTableau lam.shape γ.shape μ.shape) {r : ℕ}
    (hr : r < n) :
    lrHiveFun T (Vertex.ofIJ n (r + 1) (r + 1) le_rfl hr) -
        lrHiveFun T (Vertex.ofIJ n r r le_rfl (by omega)) = (γ.shape.rowLen r : ℤ) := by
  have h1 := lrHiveFun_step_i T (i := r) (j := r + 1) (Nat.lt_succ_self r) hr
  have h2 := lrHiveFun_step_j T (i := r) (j := r) le_rfl hr
  have hdiag : ∑ s ∈ Finset.range (r + 1), (T.1.rowCount s r : ℤ) = (T.1.rowCount r r : ℤ) := by
    rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
    intro s hs
    simp [lrTableau_rowCount_eq_zero_of_lt T (Finset.mem_range.mp hs)]
  have hrow : ∑ k ∈ Finset.range (r + 1), T.1.rowCount r k =
      γ.shape.rowLen r - lam.shape.rowLen r :=
    T.1.sum_range_rowCount_of_forall_lt fun j _ _ => Nat.lt_succ_of_le (T.entry_le r j)
  have hrowZ : (lam.shape.rowLen r : ℤ) + ∑ k ∈ Finset.range (r + 1), (T.1.rowCount r k : ℤ) =
      (γ.shape.rowLen r : ℤ) := by
    have hle := YoungDiagram.rowLen_le_of_le T.1.le r
    have hrow' : ∑ k ∈ Finset.range (r + 1), (T.1.rowCount r k : ℤ) =
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
        Vertex.ofIJ n 0 (i.val + 1) (Nat.zero_le _) i.isLt :=
      (Vertex.ofIJ_zero_left n (i.val + 1) i.isLt).symm
    have hcast : Vertex.edgePoint n 0 i.castSucc =
        Vertex.ofIJ n 0 i.val (Nat.zero_le _) i.isLt.le :=
      (Vertex.ofIJ_zero_left n i.val i.isLt.le).symm
    rw [hsucc, hcast, mk_apply, mk_apply, lrHiveFun_step_j T (Nat.zero_le _) i.isLt,
      Finset.sum_range_zero, add_zero, DominantWeight.natCast_rowLen_shape hlam i]
  · simp only [Fin.mk_one, Fin.isValue, boundary_apply, productBoundary_one]
    have hsucc : Vertex.edgePoint n 1 i.succ = Vertex.ofIJ n (i.val + 1) n i.isLt le_rfl :=
      (Vertex.ofIJ_right_eq n (i.val + 1) i.isLt).symm
    have hcast : Vertex.edgePoint n 1 i.castSucc = Vertex.ofIJ n i.val n i.isLt.le le_rfl :=
      (Vertex.ofIJ_right_eq n i.val i.isLt.le).symm
    rw [hsucc, hcast, mk_apply, mk_apply, lrHiveFun_step_i T i.isLt le_rfl]
    have hcont : ∑ r ∈ Finset.range n, T.1.rowCount r i.val = μ.shape.rowLen i.val := by
      rw [T.1.sum_range_rowCount_eq_content i.val (DominantWeight.colLen_zero_shape_le γ)]
      exact congrFun T.2.1 i.val
    have hcontZ : ∑ r ∈ Finset.range n, (T.1.rowCount r i.val : ℤ) = (μ.shape.rowLen i.val : ℤ) :=
      by exact_mod_cast hcont
    rw [hcontZ, DominantWeight.natCast_rowLen_shape hμ i]
  · simp only [Fin.reduceFinMk, Fin.isValue, boundary_apply, productBoundary_two,
      DominantWeight.dual_apply]
    have hsucc : Vertex.edgePoint n 2 i.succ =
        Vertex.ofIJ n i.rev.val i.rev.val le_rfl i.rev.isLt.le := by
      rw [Vertex.ofIJ_diag]; congr 1; ext; simp [Fin.val_rev]; omega
    have hcast : Vertex.edgePoint n 2 i.castSucc =
        Vertex.ofIJ n (i.rev.val + 1) (i.rev.val + 1) le_rfl i.rev.isLt := by
      rw [Vertex.ofIJ_diag]; congr 1; ext; simp [Fin.val_rev]; omega
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

@[simp] theorem hiveOfLRTableau_apply_ofIJ (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (hγ : γ.IsPolynomial) (T : LRTableau lam.shape γ.shape μ.shape) {i j : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) :
    (hiveOfLRTableau hlam hμ hγ T).1 (Vertex.ofIJ n i j hij hjn) =
      (∑ r ∈ Finset.range j, (lam.shape.rowLen r : ℤ)) +
        ∑ k ∈ Finset.range i, ∑ r ∈ Finset.range j, (T.1.rowCount r k : ℤ) :=
  lrHiveFun_ofIJ T hij hjn

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
      h (Vertex.ofIJ n (k + 1) (r + 1) (by omega) hr) -
        h (Vertex.ofIJ n k (r + 1) (by omega) hr) -
        h (Vertex.ofIJ n (k + 1) r hk hr.le) +
        h (Vertex.ofIJ n k r hk.le hr.le)
    else if k = r then
      h (Vertex.ofIJ n (r + 1) (r + 1) le_rfl hr) -
        h (Vertex.ofIJ n r (r + 1) (Nat.le_succ r) hr)
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

/-- Column telescoping of `hiveEntryInt`: for `k < j ≤ n`, summing `hiveEntryInt h r k` over
`r < j` gives `h(k + 1, j) - h(k, j)`. -/
private theorem sum_range_hiveEntryInt_col (h : IntegerHive n) {k j : ℕ}
    (hkj : k < j) (hjn : j ≤ n) :
    ∑ r ∈ Finset.range j, hiveEntryInt h r k =
      h (Vertex.ofIJ n (k + 1) j hkj hjn) - h (Vertex.ofIJ n k j hkj.le hjn) := by
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
      (h (Vertex.ofIJ n i (r + 1) (by omega) hr) - h (Vertex.ofIJ n i r hir hr.le)) -
        (h (Vertex.ofIJ n 0 (r + 1) (Nat.zero_le _) hr) -
          h (Vertex.ofIJ n 0 r (Nat.zero_le _) hr.le)) := by
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
      (h (Vertex.ofIJ n (r + 1) (r + 1) le_rfl hr) - h (Vertex.ofIJ n r r le_rfl hr.le)) -
        (h (Vertex.ofIJ n 0 (r + 1) (Nat.zero_le _) hr) -
          h (Vertex.ofIJ n 0 r (Nat.zero_le _) hr.le)) := by
  have heq : ∑ k ∈ Finset.range i, hiveEntryInt h r k =
      ∑ k ∈ Finset.range (r + 1), hiveEntryInt h r k := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hri
    rw [Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range d) fun l _ =>
      hiveEntryInt_eq_zero_of_lt h (by omega), add_zero]
  rw [heq, Finset.sum_range_succ, sum_range_hiveEntryInt_row_le h le_rfl hr]
  simp only [hiveEntryInt, hr, ↓reduceDIte, lt_irrefl, ↓reduceIte]
  abel

variable {lam μ γ : DominantWeight n}

private theorem step_ofIJ_zero_left (h : FixedIntegerHive (productBoundary lam μ γ))
    {j : ℕ} (hj : j < n) :
    h.1 (Vertex.ofIJ n 0 (j + 1) (Nat.zero_le _) hj) -
        h.1 (Vertex.ofIJ n 0 j (Nat.zero_le _) hj.le) = lam.1 ⟨j, hj⟩ := by
  have hb := congrFun (congrFun h.2 0) ⟨j, hj⟩
  rw [boundary_apply, productBoundary_zero] at hb
  have h1 : Vertex.edgePoint n 0 (⟨j, hj⟩ : Fin n).succ =
      Vertex.ofIJ n 0 (j + 1) (Nat.zero_le _) hj :=
    (Vertex.ofIJ_zero_left n (j + 1) hj).symm
  have h2 : Vertex.edgePoint n 0 (⟨j, hj⟩ : Fin n).castSucc =
      Vertex.ofIJ n 0 j (Nat.zero_le _) hj.le :=
    (Vertex.ofIJ_zero_left n j hj.le).symm
  rwa [h1, h2] at hb

private theorem step_ofIJ_right_eq (h : FixedIntegerHive (productBoundary lam μ γ))
    {i : ℕ} (hi : i < n) :
    h.1 (Vertex.ofIJ n (i + 1) n hi le_rfl) -
        h.1 (Vertex.ofIJ n i n hi.le le_rfl) = μ.1 ⟨i, hi⟩ := by
  have hb := congrFun (congrFun h.2 1) ⟨i, hi⟩
  rw [boundary_apply, productBoundary_one] at hb
  have h1 : Vertex.edgePoint n 1 (⟨i, hi⟩ : Fin n).succ = Vertex.ofIJ n (i + 1) n hi le_rfl :=
    (Vertex.ofIJ_right_eq n (i + 1) hi).symm
  have h2 : Vertex.edgePoint n 1 (⟨i, hi⟩ : Fin n).castSucc = Vertex.ofIJ n i n hi.le le_rfl :=
    (Vertex.ofIJ_right_eq n i hi.le).symm
  rwa [h1, h2] at hb

private theorem step_ofIJ_diag (h : FixedIntegerHive (productBoundary lam μ γ))
    {r : ℕ} (hr : r < n) :
    h.1 (Vertex.ofIJ n (r + 1) (r + 1) le_rfl hr) -
        h.1 (Vertex.ofIJ n r r le_rfl hr.le) = γ.1 ⟨r, hr⟩ := by
  let i : Fin n := ⟨n - 1 - r, by omega⟩
  have hirev : i.rev = ⟨r, hr⟩ := by ext; simp [i, Fin.val_rev]; omega
  have hb := congrFun (congrFun h.2 2) i
  rw [boundary_apply, productBoundary_two, DominantWeight.dual_apply, hirev] at hb
  have h1 : Vertex.edgePoint n 2 i.succ = Vertex.ofIJ n r r le_rfl hr.le := by
    rw [Vertex.ofIJ_diag]; congr 1; ext; simp [i]; omega
  have h2 : Vertex.edgePoint n 2 i.castSucc = Vertex.ofIJ n (r + 1) (r + 1) le_rfl hr := by
    rw [Vertex.ofIJ_diag]; congr 1; ext; simp [i]; omega
  rw [h1, h2] at hb
  linarith

/-- Every extracted integer entry `hiveEntryInt h.1 r k` is nonnegative when `μ` is polynomial. -/
private theorem hiveEntryInt_nonneg (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r k : ℕ) :
    0 ≤ hiveEntryInt h.1 r k := by
  by_cases hr : r < n
  · by_cases hk : k < r
    · simp only [hiveEntryInt, hr, ↓reduceDIte, hk]
      linarith [h.1.le_ofIJ_upright hk hr]
    · by_cases hkeq : k = r
      · subst k
        -- Prove `0 ≤ hiveEntryInt h.1 r r` by downward induction on `r` from `n - 1`.
        suffices ∀ d r, r + d + 1 = n → 0 ≤ hiveEntryInt h.1 r r from
          this (n - 1 - r) r (by omega)
        intro d
        induction d with
        | zero =>
          intro r hdn
          have hr' : r < n := by omega
          have h1 : hiveEntryInt h.1 r r =
              h.1 (Vertex.ofIJ n (r + 1) n (by omega) le_rfl) -
                h.1 (Vertex.ofIJ n r n (by omega) le_rfl) := by
            simp only [hiveEntryInt, hr', ↓reduceDIte, lt_irrefl, ↓reduceIte]
            congr 2 <;> simp [hdn]
          rw [h1, step_ofIJ_right_eq h hr']
          exact (DominantWeight.isPolynomial_def _).mp hμ ⟨r, hr'⟩
        | succ d ih =>
          intro r hdn
          have hr' : r < n := by omega
          have hr1 : r + 1 < n := by omega
          have hstep : hiveEntryInt h.1 (r + 1) (r + 1) ≤ hiveEntryInt h.1 r r := by
            simp only [hiveEntryInt, hr', hr1, ↓reduceDIte, lt_irrefl, ↓reduceIte]
            linarith [h.1.le_ofIJ_left (i := r) (j := r + 1) (Nat.lt_succ_self r) hr1]
          exact (ih (r + 1) (by omega)).trans hstep
      · simp [hiveEntryInt, hr, hk, hkeq]
  · simp [hiveEntryInt, hr]

private theorem natCast_hiveEntryNat (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r k : ℕ) :
    (hiveEntryNat h.1 r k : ℤ) = hiveEntryInt h.1 r k :=
  Int.toNat_of_nonneg (hiveEntryInt_nonneg hμ h r k)

private theorem shape_le_of_fixedIntegerHive (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    lam.shape ≤ γ.shape := by
  have hγ : γ.IsPolynomial := isPolynomial_of_productBoundary h.2 hlam hμ
  refine YoungDiagram.le_of_forall_rowLen_le fun r => ?_
  by_cases hr : r < n
  · have hfull := sum_range_hiveEntryInt_row_full h.1 (i := n) hr hr
    rw [step_ofIJ_diag h hr, step_ofIJ_zero_left h hr] at hfull
    have hnn : 0 ≤ ∑ k ∈ Finset.range n, hiveEntryInt h.1 r k :=
      Finset.sum_nonneg fun k _ => hiveEntryInt_nonneg hμ h r k
    have h1 : (lam.shape.rowLen r : ℤ) = lam.1 ⟨r, hr⟩ :=
      DominantWeight.natCast_rowLen_shape hlam ⟨r, hr⟩
    have h2 : (γ.shape.rowLen r : ℤ) = γ.1 ⟨r, hr⟩ :=
      DominantWeight.natCast_rowLen_shape hγ ⟨r, hr⟩
    omega
  · simp [DominantWeight.rowLen_shape_eq_zero_of_le _ (Nat.le_of_not_lt hr)]

private theorem sum_range_hiveEntryNat_row (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r : ℕ) :
    ∑ k ∈ Finset.range n, hiveEntryNat h.1 r k = γ.shape.rowLen r - lam.shape.rowLen r := by
  have hγ : γ.IsPolynomial := isPolynomial_of_productBoundary h.2 hlam hμ
  by_cases hr : r < n
  · have hfull := sum_range_hiveEntryInt_row_full h.1 (i := n) hr hr
    rw [step_ofIJ_diag h hr, step_ofIJ_zero_left h hr] at hfull
    have hZ : ((∑ k ∈ Finset.range n, hiveEntryNat h.1 r k : ℕ) : ℤ) =
        ∑ k ∈ Finset.range n, hiveEntryInt h.1 r k := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun k _ => natCast_hiveEntryNat hμ h r k
    have h1 : (lam.shape.rowLen r : ℤ) = lam.1 ⟨r, hr⟩ :=
      DominantWeight.natCast_rowLen_shape hlam ⟨r, hr⟩
    have h2 : (γ.shape.rowLen r : ℤ) = γ.1 ⟨r, hr⟩ :=
      DominantWeight.natCast_rowLen_shape hγ ⟨r, hr⟩
    have := YoungDiagram.rowLen_le_of_le (shape_le_of_fixedIntegerHive hlam hμ h) r
    omega
  · have hnr : n ≤ r := Nat.le_of_not_lt hr
    simp [hiveEntryNat, hiveEntryInt_eq_zero_of_le h.1 hnr,
      DominantWeight.rowLen_shape_eq_zero_of_le _ hnr]

private theorem sum_range_hiveEntryNat_col (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (k : ℕ) :
    ∑ r ∈ Finset.range n, hiveEntryNat h.1 r k = μ.shape.rowLen k := by
  by_cases hk : k < n
  · have hZ : ((∑ r ∈ Finset.range n, hiveEntryNat h.1 r k : ℕ) : ℤ) =
        ∑ r ∈ Finset.range n, hiveEntryInt h.1 r k := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun r _ => natCast_hiveEntryNat hμ h r k
    have hμk : (μ.shape.rowLen k : ℤ) = μ.1 ⟨k, hk⟩ :=
      DominantWeight.natCast_rowLen_shape hμ ⟨k, hk⟩
    rw [sum_range_hiveEntryInt_col h.1 hk le_rfl, step_ofIJ_right_eq h hk, ← hμk] at hZ
    exact Int.ofNat.inj hZ
  · have hnk : n ≤ k := Nat.le_of_not_lt hk
    simp [hiveEntryNat, hiveEntryInt_eq_zero_of_le_right h.1 hnk,
      DominantWeight.rowLen_shape_eq_zero_of_le _ hnk]

private theorem hiveEntryNat_col_strict (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r x : ℕ) :
    lam.shape.rowLen (r + 1) + ∑ k ∈ Finset.range (x + 1), hiveEntryNat h.1 (r + 1) k ≤
      lam.shape.rowLen r + ∑ k ∈ Finset.range x, hiveEntryNat h.1 r k := by
  by_cases hr1 : r + 1 < n
  · have hr : r < n := by omega
    suffices ((lam.shape.rowLen (r + 1) : ℤ) +
        ∑ k ∈ Finset.range (x + 1), hiveEntryInt h.1 (r + 1) k) ≤
        (lam.shape.rowLen r : ℤ) + ∑ k ∈ Finset.range x, hiveEntryInt h.1 r k by
      have hL : ((∑ k ∈ Finset.range (x + 1), hiveEntryNat h.1 (r + 1) k : ℕ) : ℤ) =
          ∑ k ∈ Finset.range (x + 1), hiveEntryInt h.1 (r + 1) k := by
        rw [Nat.cast_sum]
        exact Finset.sum_congr rfl fun k _ => natCast_hiveEntryNat hμ h (r + 1) k
      have hR : ((∑ k ∈ Finset.range x, hiveEntryNat h.1 r k : ℕ) : ℤ) =
          ∑ k ∈ Finset.range x, hiveEntryInt h.1 r k := by
        rw [Nat.cast_sum]
        exact Finset.sum_congr rfl fun k _ => natCast_hiveEntryNat hμ h r k
      omega
    rw [DominantWeight.natCast_rowLen_shape hlam ⟨r + 1, hr1⟩,
      DominantWeight.natCast_rowLen_shape hlam ⟨r, hr⟩]
    rcases le_or_gt x r with hxr | hrx
    · rw [sum_range_hiveEntryInt_row_le h.1 (by omega : x + 1 ≤ r + 1) hr1,
        sum_range_hiveEntryInt_row_le h.1 hxr hr,
        step_ofIJ_zero_left h hr1, step_ofIJ_zero_left h hr]
      linarith [h.1.le_ofIJ_right hxr (by omega : r + 2 ≤ n)]
    · rw [sum_range_hiveEntryInt_row_full h.1 (by omega : r + 2 ≤ x + 1) hr1,
        sum_range_hiveEntryInt_row_full h.1 hrx hr,
        step_ofIJ_diag h hr1, step_ofIJ_diag h hr,
        step_ofIJ_zero_left h hr1, step_ofIJ_zero_left h hr]
      have hanti : γ.1 ⟨r + 1, hr1⟩ ≤ γ.1 ⟨r, hr⟩ :=
        γ.antitone (Fin.mk_le_mk.mpr (Nat.le_succ r))
      linarith
  · have hnr : n ≤ r + 1 := Nat.le_of_not_lt hr1
    have h0 : ∑ k ∈ Finset.range (x + 1), hiveEntryNat h.1 (r + 1) k = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hiveEntryNat, hiveEntryInt_eq_zero_of_le h.1 hnr]
    rw [DominantWeight.rowLen_shape_eq_zero_of_le _ hnr, h0, add_zero]
    exact Nat.zero_le _

private theorem hiveEntryNat_lattice (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (k x : ℕ) :
    ∑ r ∈ Finset.range (x + 1), hiveEntryNat h.1 r (k + 1) ≤
      ∑ r ∈ Finset.range x, hiveEntryNat h.1 r k := by
  suffices ∑ r ∈ Finset.range (x + 1), hiveEntryInt h.1 r (k + 1) ≤
      ∑ r ∈ Finset.range x, hiveEntryInt h.1 r k by
    have hL : ((∑ r ∈ Finset.range (x + 1), hiveEntryNat h.1 r (k + 1) : ℕ) : ℤ) =
        ∑ r ∈ Finset.range (x + 1), hiveEntryInt h.1 r (k + 1) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun r _ => natCast_hiveEntryNat hμ h r (k + 1)
    have hR : ((∑ r ∈ Finset.range x, hiveEntryNat h.1 r k : ℕ) : ℤ) =
        ∑ r ∈ Finset.range x, hiveEntryInt h.1 r k := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun r _ => natCast_hiveEntryNat hμ h r k
    omega
  rcases le_or_gt x k with hxk | hkx
  · rw [Finset.sum_eq_zero fun r hr => hiveEntryInt_eq_zero_of_lt h.1 (by
      have := Finset.mem_range.mp hr; omega)]
    exact Finset.sum_nonneg fun r _ => hiveEntryInt_nonneg hμ h r k
  · by_cases hk1 : k + 1 < n
    · rcases le_or_gt (x + 1) n with hx1 | hnx
      · rw [sum_range_hiveEntryInt_col h.1 (by omega : k + 1 < x + 1) hx1,
          sum_range_hiveEntryInt_col h.1 hkx (by omega : x ≤ n)]
        linarith [h.1.le_ofIJ_left hkx hx1]
      · have heq1 : ∑ r ∈ Finset.range (x + 1), hiveEntryInt h.1 r (k + 1) =
            ∑ r ∈ Finset.range n, hiveEntryInt h.1 r (k + 1) := by
          obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (by omega : n ≤ x + 1)
          rw [hd, Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range d) fun l _ =>
            hiveEntryInt_eq_zero_of_le h.1 (Nat.le_add_right n l), add_zero]
        have heq2 : ∑ r ∈ Finset.range x, hiveEntryInt h.1 r k =
            ∑ r ∈ Finset.range n, hiveEntryInt h.1 r k := by
          obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (by omega : n ≤ x)
          rw [hd, Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range d) fun l _ =>
            hiveEntryInt_eq_zero_of_le h.1 (Nat.le_add_right n l), add_zero]
        rw [heq1, heq2, sum_range_hiveEntryInt_col h.1 hk1 le_rfl,
          sum_range_hiveEntryInt_col h.1 (by omega : k < n) le_rfl,
          step_ofIJ_right_eq h hk1, step_ofIJ_right_eq h (by omega : k < n)]
        exact μ.antitone (Fin.mk_le_mk.mpr (Nat.le_succ k))
    · rw [Finset.sum_eq_zero fun r _ =>
        hiveEntryInt_eq_zero_of_le_right h.1 (Nat.le_of_not_lt hk1)]
      exact Finset.sum_nonneg fun r _ => hiveEntryInt_nonneg hμ h r k

/-- The Littlewood–Richardson tableau extracted from a fixed-boundary integer hive `h` on
polynomial dominant weights `λ, μ` (with `γ` automatically polynomial from the existence of `h`). -/
def lrTableauOfHive (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) : LRTableau lam.shape γ.shape μ.shape :=
  let T : SkewSemistandardYoungTableau lam.shape γ.shape :=
    SkewSemistandardYoungTableau.ofRowCount
      (shape_le_of_fixedIntegerHive hlam hμ h) n (hiveEntryNat h.1)
      (sum_range_hiveEntryNat_row hlam hμ h)
      (hiveEntryNat_col_strict hlam hμ h)
  have hrc : ∀ r k, T.rowCount r k = hiveEntryNat h.1 r k :=
    SkewSemistandardYoungTableau.rowCount_ofRowCount _ _ _ fun r l hl => by
      simp [hiveEntryNat, hiveEntryInt_eq_zero_of_le_right h.1 hl]
  ⟨T, funext fun k => by
      rw [← T.sum_range_rowCount_eq_content k (DominantWeight.colLen_zero_shape_le γ)]
      simp_rw [hrc]
      exact sum_range_hiveEntryNat_col hμ h k,
    T.isLatticeWord_readingWord_iff.mpr fun k x => by
      simp_rw [hrc]; exact hiveEntryNat_lattice hμ h k x⟩

private theorem rowCount_lrTableauOfHive (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r k : ℕ) :
    (lrTableauOfHive hlam hμ h).1.rowCount r k = (hiveEntryInt h.1 r k).toNat :=
  SkewSemistandardYoungTableau.rowCount_ofRowCount _ _ _ (fun r l hl => by
    simp [hiveEntryNat, hiveEntryInt_eq_zero_of_le_right h.1 hl]) r k

/-- Partial-sum identity for `lrTableauOfHive`: for `k < j ≤ n`, summing the multiplicity of
letter `k` over rows `0, …, j - 1` gives the horizontal hive increment `h(k + 1, j) - h(k, j)`. -/
theorem sum_range_rowCount_lrTableauOfHive (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) {k j : ℕ}
    (hkj : k < j) (hjn : j ≤ n) :
    ∑ r ∈ Finset.range j, ((lrTableauOfHive hlam hμ h).1.rowCount r k : ℤ) =
      h.1 (Vertex.ofIJ n (k + 1) j hkj hjn) - h.1 (Vertex.ofIJ n k j hkj.le hjn) := by
  simp_rw [rowCount_lrTableauOfHive, fun r => Int.toNat_of_nonneg (hiveEntryInt_nonneg hμ h r k)]
  exact sum_range_hiveEntryInt_col h.1 hkj hjn

end InverseMap

/-! ### The hive–Littlewood–Richardson bijection (polynomial and signed weights) -/

section Equivalence

variable {n : ℕ}

private theorem shape_shift_neg_detShift (l : DominantWeight n) :
    (l.shift (-l.detShift)).shape = l.detShiftShape := by
  rw [← l.weightOfShape_detShiftShape, shape_weightOfShape l.colLen_zero_detShiftShape_le]

section FixedWeights

variable {lam μ γ : DominantWeight n}

private theorem hiveOfLRTableau_lrTableauOfHive (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (hγ : γ.IsPolynomial) (h : FixedIntegerHive (productBoundary lam μ γ)) :
    hiveOfLRTableau hlam hμ hγ (lrTableauOfHive hlam hμ h) = h := by
  refine Subtype.ext (Hive.ext fun p => ?_)
  have hp : p = Vertex.ofIJ n p.z (p.y + p.z) (Nat.le_add_left _ _)
      (by have := p.sum_eq; omega) := (Vertex.ofIJ_z_add p).symm
  rw [hp]
  suffices ∀ i j (hij : i ≤ j) (hjn : j ≤ n),
      (hiveOfLRTableau hlam hμ hγ (lrTableauOfHive hlam hμ h)).1
        (Vertex.ofIJ n i j hij hjn) = h.1 (Vertex.ofIJ n i j hij hjn) from
    this p.z (p.y + p.z) (Nat.le_add_left _ _) (by have := p.sum_eq; omega)
  intro i j hij hjn
  rw [hiveOfLRTableau_apply_ofIJ]
  simp only [rowCount_lrTableauOfHive]
  have hcast : ∀ r k, ((hiveEntryInt h.1 r k).toNat : ℤ) = hiveEntryInt h.1 r k :=
    fun r k => Int.toNat_of_nonneg (hiveEntryInt_nonneg hμ h r k)
  simp_rw [hcast]
  induction i with
  | zero =>
    rw [Finset.sum_range_zero, add_zero]
    induction j with
    | zero => simp [Vertex.ofIJ_zero_zero]
    | succ m ih =>
      have hstep := step_ofIJ_zero_left h hjn
      rw [← DominantWeight.natCast_rowLen_shape hlam ⟨m, hjn⟩] at hstep
      dsimp only at hstep
      rw [Finset.sum_range_succ, ih (by omega) (Nat.zero_le m), ← hstep]
      abel
  | succ m ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih (by omega),
      sum_range_hiveEntryInt_col h.1 hij hjn]
    abel

private theorem lrTableauOfHive_hiveOfLRTableau (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (hγ : γ.IsPolynomial) (T : LRTableau lam.shape γ.shape μ.shape) :
    lrTableauOfHive hlam hμ (hiveOfLRTableau hlam hμ hγ T) = T := by
  refine Subtype.ext (SkewSemistandardYoungTableau.eq_of_rowCount_eq fun r k => ?_)
  rw [rowCount_lrTableauOfHive]
  suffices hiveEntryInt (hiveOfLRTableau hlam hμ hγ T).1 r k = (T.1.rowCount r k : ℤ) by
    rw [this, Int.toNat_natCast]
  by_cases hr : r < n
  · by_cases hk : k < r
    · simp only [hiveEntryInt, hr, ↓reduceDIte, hk]
      have h1 := lrHiveFun_step_i T (i := k) (j := r + 1) (by omega) hr
      have h2 := lrHiveFun_step_i T (i := k) (j := r) hk hr.le
      rw [Finset.sum_range_succ] at h1
      change lrHiveFun T _ - lrHiveFun T _ - lrHiveFun T _ + lrHiveFun T _ = _
      linarith
    · by_cases hkeq : k = r
      · subst k
        simp only [hiveEntryInt, hr, ↓reduceDIte, lt_irrefl, ↓reduceIte]
        have h1 := lrHiveFun_step_i T (i := r) (j := r + 1) (Nat.lt_succ_self r) hr
        rw [Finset.sum_range_succ, Finset.sum_eq_zero fun s hs => by
          simp [lrTableau_rowCount_eq_zero_of_lt T (Finset.mem_range.mp hs)], zero_add] at h1
        exact h1
      · simp only [hiveEntryInt, hr, ↓reduceDIte, hk, hkeq, ↓reduceIte]
        rw [lrTableau_rowCount_eq_zero_of_lt T (by omega), Nat.cast_zero]
  · rw [hiveEntryInt_eq_zero_of_le _ (Nat.le_of_not_lt hr),
      T.1.rowCount_eq_zero_of_colLen_le
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

@[simp] theorem fixedIntegerHiveEquivLRTableau_apply (hlam : lam.IsPolynomial)
    (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    fixedIntegerHiveEquivLRTableau hlam hμ hγ h = lrTableauOfHive hlam hμ h := (rfl)

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

/-- Shift-independent cardinality identity for arbitrary signed dominant weights. -/
theorem hiveCount_productBoundary_eq_natCard_lrTableau_of_shift {a b : ℤ}
    (hlam : (lam.shift a).IsPolynomial) (hμ : (μ.shift b).IsPolynomial)
    (hγ : (γ.shift (a + b)).IsPolynomial) :
    hiveCount (productBoundary lam μ γ) =
      Nat.card (LRTableau (lam.shift a).shape (γ.shift (a + b)).shape (μ.shift b).shape) := by
  rw [← natCard_fixedIntegerHive]
  exact Nat.card_congr (fixedIntegerHiveEquivLRTableauShift hlam hμ hγ)

private theorem isPolynomial_shift_neg_detShift_add
    (hshift : lam.detShift + μ.detShift ≤ γ.detShift) :
    (γ.shift (-(lam.detShift + μ.detShift))).IsPolynomial := by
  cases n with
  | zero => exact (DominantWeight.isPolynomial_def _).mpr fun i => i.elim0
  | succ m =>
    rw [DominantWeight.isPolynomial_iff_zero_le_detShift, DominantWeight.detShift_shift]
    linarith

/-- Canonical determinant-shift bijection for arbitrary signed dominant weights `λ, μ, γ` satisfying
the necessary lower-coordinate condition `λ.detShift + μ.detShift ≤ γ.detShift`. -/
def fixedIntegerHiveEquivLRTableauDetShift
    (hshift : lam.detShift + μ.detShift ≤ γ.detShift) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      LRTableau lam.detShiftShape (γ.shift (-(lam.detShift + μ.detShift))).shape
        μ.detShiftShape := by
  have hγ := isPolynomial_shift_neg_detShift_add hshift
  have hsum : -lam.detShift + -μ.detShift = -(lam.detShift + μ.detShift) := by omega
  have he := fixedIntegerHiveEquivLRTableauShift (lam := lam) (μ := μ) (γ := γ)
    (a := -lam.detShift) (b := -μ.detShift)
    lam.isPolynomial_shift_neg_detShift μ.isPolynomial_shift_neg_detShift (hsum.symm ▸ hγ)
  rwa [shape_shift_neg_detShift lam, shape_shift_neg_detShift μ, hsum] at he

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

/-! ### The hive Littlewood–Richardson rule for Schur polynomials -/

section SchurRule

/-- **The hive Littlewood–Richardson rule for Schur polynomials**: over any commutative semiring
`R`, the product of the Schur polynomials of two polynomial dominant weights `λ, μ` expands as a
finitely supported sum over dominant weights `γ` with multiplicity
`hiveCount (productBoundary λ μ γ)`. -/
theorem schur_mul_eq_finsum_hiveCount {n : ℕ} {R : Type*} [CommSemiring R]
    (lam μ : DominantWeight n) (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) :
    diagramSchurPoly n R lam.shape * diagramSchurPoly n R μ.shape =
      ∑ᶠ γ : DominantWeight n,
        hiveCount (productBoundary lam μ γ) • diagramSchurPoly n R γ.shape := by
  classical
  rw [diagramSchurPoly_mul_diagramSchurPoly_eq_sum_natCard_lrTableau,
    sum_nsmul_diagramSchurPoly_eq_sum_colLen_le]
  let e : {ν : (lam.shape.card + μ.shape.card).Partition //
      (YoungDiagram.ofPartition ν).colLen 0 ≤ n} ↪ DominantWeight n :=
    ⟨fun ν => weightOfShape n (YoungDiagram.ofPartition ν.1), fun ν₁ ν₂ h => Subtype.ext <|
      YoungDiagram.ofPartition_injective <| by
        have h' := congrArg DominantWeight.shape h
        rwa [shape_weightOfShape ν₁.2, shape_weightOfShape ν₂.2] at h'⟩
  have hsupp : Function.support (fun γ : DominantWeight n =>
      hiveCount (productBoundary lam μ γ) • diagramSchurPoly n R γ.shape) ⊆
      (Finset.univ.map e : Set (DominantWeight n)) := by
    intro γ hγ
    have hpos : 0 < hiveCount (productBoundary lam μ γ) := Nat.pos_of_ne_zero fun h0 => by
      simp [h0] at hγ
    obtain ⟨⟨h, hb⟩⟩ := hiveCount_pos_iff.mp hpos
    have hγp : γ.IsPolynomial := isPolynomial_of_productBoundary hb hlam hμ
    let T := lrTableauOfHive hlam hμ ⟨h, hb⟩
    refine Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨⟨γ.shape.toPartition T.card_eq, by simp⟩,
      Finset.mem_univ _, ?_⟩)
    change weightOfShape n (YoungDiagram.ofPartition (γ.shape.toPartition T.card_eq)) = γ
    rw [YoungDiagram.ofPartition_toPartition, weightOfShape_shape hγp]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_map]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have hpoly : (e ν).IsPolynomial := isPolynomial_weightOfShape n _
  have hshape : (e ν).shape = YoungDiagram.ofPartition ν.1 := shape_weightOfShape ν.2
  rw [hiveCount_productBoundary_eq_natCard_lrTableau hlam hμ hpoly, hshape]

end SchurRule

/-! ### `GLₙ(ℂ)` tensor-product multiplicities and commutativity -/

section TensorMultiplicities

/-- Expand `Module.finrank ℂ (V_γ ⟶ V_λ ⊗ V_μ)` via the Littlewood–Richardson direct-sum
decomposition of `rationalWeylRep` and Schur's lemma. -/
private theorem finrank_hom_tprod_rationalWeylFDRep_eq_sum {n : ℕ} (lam μ γ : DominantWeight n) :
    Module.finrank ℂ
        (rationalWeylFDRep ℂ n γ ⟶ rationalWeylFDRep ℂ n lam ⊗ rationalWeylFDRep ℂ n μ) =
      ∑ ν : {ν : (lam.detShiftShape.card + μ.detShiftShape.card).Partition //
          (YoungDiagram.ofPartition ν).colLen 0 ≤ n},
        if γ = (weightOfShape n (YoungDiagram.ofPartition ν.1)).shift
            (lam.detShift + μ.detShift) then
          Nat.card {T : BoundedSSYT n μ.detShiftShape // T.1.IsYamanouchi lam.detShiftShape ∧
            ∀ i, lam.detShiftShape.rowLen i + T.1.content i =
              (YoungDiagram.ofPartition ν.1).rowLen i}
        else 0 := by
  classical
  let ι := Σ ν : {ν : (lam.detShiftShape.card + μ.detShiftShape.card).Partition //
      (YoungDiagram.ofPartition ν).colLen 0 ≤ n},
    {T : BoundedSSYT n μ.detShiftShape // T.1.IsYamanouchi lam.detShiftShape ∧
      ∀ i, lam.detShiftShape.rowLen i + T.1.content i = (YoungDiagram.ofPartition ν.1).rowLen i}
  let w : ι → DominantWeight n := fun p =>
    (weightOfShape n (YoungDiagram.ofPartition p.1.1)).shift (lam.detShift + μ.detShift)
  let _ (p : ι) : AddCommGroup (weylModuleOfShape ℂ n (w p).detShiftShape).toSubmodule :=
    inferInstance
  obtain ⟨e⟩ := nonempty_equiv_tprod_rationalWeylRep n lam μ
  let e₁ := (FDRep.forget₂HomLinearEquiv (rationalWeylFDRep ℂ n γ)
    (rationalWeylFDRep ℂ n lam ⊗ rationalWeylFDRep ℂ n μ)).symm ≪≫ₗ Rep.homLinearEquiv _ _
  let e₂ := Representation.Equiv.intertwiningMapCongr
    (Representation.Equiv.refl (rationalWeylRep ℂ n γ)) e
  let e₃ := Representation.IntertwiningMap.directSumLinearEquiv
    (rationalWeylRep ℂ n γ) (fun p : ι => rationalWeylRep ℂ n (w p))
  let e₄ : (∀ p : ι, Representation.IntertwiningMap (rationalWeylRep ℂ n γ)
      (rationalWeylRep ℂ n (w p))) ≃ₗ[ℂ]
      (∀ p : ι, rationalWeylFDRep ℂ n γ ⟶ rationalWeylFDRep ℂ n (w p)) :=
    LinearEquiv.piCongrRight fun p =>
      ((FDRep.forget₂HomLinearEquiv (rationalWeylFDRep ℂ n γ)
        (rationalWeylFDRep ℂ n (w p))).symm ≪≫ₗ Rep.homLinearEquiv _ _).symm
  have hfin : ∀ p : ι, Module.Finite ℂ
      (rationalWeylFDRep ℂ n γ ⟶ rationalWeylFDRep ℂ n (w p)) := fun _ => inferInstance
  rw [(e₁ ≪≫ₗ e₂ ≪≫ₗ e₃ ≪≫ₗ e₄).finrank_eq, Module.finrank_pi_fintype]
  have hdim (p : ι) : Module.finrank ℂ (rationalWeylFDRep ℂ n γ ⟶ rationalWeylFDRep ℂ n (w p)) =
      if γ = w p then 1 else 0 := by
    rw [FDRep.finrank_hom_simple_simple, nonempty_iso_rationalWeylFDRep_iff ℂ]
    by_cases h : γ = w p <;> simp [h]
  simp_rw [hdim]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases h : γ = (weightOfShape n (YoungDiagram.ofPartition ν.1)).shift
      (lam.detShift + μ.detShift)
  · simp [w, h, Nat.card_eq_fintype_card]
  · simp [w, h]

private theorem natCard_boundedSSYT_isYamanouchi_eq_natCard_lrTableau {n : ℕ}
    {inner outer μ : YoungDiagram} (houter : outer.colLen 0 ≤ n) :
    Nat.card {T : BoundedSSYT n μ // T.1.IsYamanouchi inner ∧
        ∀ i, inner.rowLen i + T.1.content i = outer.rowLen i} =
      Nat.card (LRTableau inner outer μ) := by
  rw [natCard_lrTableau_eq_natCard_isYamanouchi]
  exact Nat.card_congr
    { toFun := fun T => ⟨T.1.1, T.2.1, T.2.2⟩
      invFun := fun T => ⟨⟨T.1, fun i c hc =>
        (SemistandardYoungTableau.apply_lt_colLen_zero_of_rowLen_add_content_eq
          T.2.2 hc).trans_le houter⟩, T.2.1, T.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem detShift_le_of_eq_shift_weightOfShape {n : ℕ} {lam μ γ : DominantWeight n}
    {ν : YoungDiagram} (h : γ = (weightOfShape n ν).shift (lam.detShift + μ.detShift)) :
    lam.detShift + μ.detShift ≤ γ.detShift := by
  cases n with
  | zero => simp
  | succ m =>
    have hdet := congrArg DominantWeight.detShift h
    rw [DominantWeight.detShift_shift] at hdet
    have hnn : 0 ≤ (weightOfShape (m + 1) ν).detShift :=
      (DominantWeight.isPolynomial_iff_zero_le_detShift _).mp (isPolynomial_weightOfShape _ _)
    linarith

/-- **Hive tensor-product multiplicity theorem for `GLₙ(ℂ)`**: for arbitrary dominant weights
`λ, μ, γ` of `GLₙ(ℂ)`, the multiplicity of the irreducible rational Weyl module `V_γ` in
`V_λ ⊗ V_μ` equals `hiveCount (productBoundary λ μ γ)`. -/
theorem finrank_hom_eq_hiveCount {n : ℕ} (lam μ γ : DominantWeight n) :
    Module.finrank ℂ
        (rationalWeylFDRep ℂ n γ ⟶ rationalWeylFDRep ℂ n lam ⊗ rationalWeylFDRep ℂ n μ) =
      hiveCount (productBoundary lam μ γ) := by
  classical
  rw [finrank_hom_tprod_rationalWeylFDRep_eq_sum,
    hiveCount_productBoundary_eq_ite_natCard_lrTableau]
  split_ifs with hshift
  · set γ₀ : DominantWeight n := γ.shift (-(lam.detShift + μ.detShift))
    have hγ₀ : γ₀.IsPolynomial := isPolynomial_shift_neg_detShift_add hshift
    have hw_iff (ν : {ν : (lam.detShiftShape.card + μ.detShiftShape.card).Partition //
        (YoungDiagram.ofPartition ν).colLen 0 ≤ n}) :
        γ = (weightOfShape n (YoungDiagram.ofPartition ν.1)).shift (lam.detShift + μ.detShift) ↔
          γ₀.shape = YoungDiagram.ofPartition ν.1 := by
      refine ⟨fun h => by subst h; simp [γ₀, shape_weightOfShape ν.2], fun h => ?_⟩
      have h' : γ₀ = weightOfShape n (YoungDiagram.ofPartition ν.1) := by
        rw [← h, weightOfShape_shape hγ₀]
      simpa [γ₀] using congrArg (fun x : DominantWeight n =>
        x.shift (lam.detShift + μ.detShift)) h'
    by_cases hcard : γ₀.shape.card = lam.detShiftShape.card + μ.detShiftShape.card
    · let ν₀ : {ν : (lam.detShiftShape.card + μ.detShiftShape.card).Partition //
          (YoungDiagram.ofPartition ν).colLen 0 ≤ n} :=
        ⟨γ₀.shape.toPartition hcard, by simp⟩
      rw [Finset.sum_eq_single ν₀]
      · have hpos : γ = (weightOfShape n (YoungDiagram.ofPartition ν₀.1)).shift
            (lam.detShift + μ.detShift) := (hw_iff ν₀).mpr (by simp [ν₀])
        simp only [hpos, ↓reduceIte]
        simpa [ν₀] using natCard_boundedSSYT_isYamanouchi_eq_natCard_lrTableau
          (inner := lam.detShiftShape) (μ := μ.detShiftShape) γ₀.colLen_zero_shape_le
      · intro ν _ hne
        split_ifs with heq
        · exact absurd (Subtype.ext <| YoungDiagram.ofPartition_injective <| by
            have hshape := (hw_iff ν).mp heq; simp [ν₀, ← hshape]) hne
        · rfl
      · exact fun h => absurd (Finset.mem_univ _) h
    · have hempty : IsEmpty (LRTableau lam.detShiftShape γ₀.shape μ.detShiftShape) :=
        ⟨fun T => hcard T.card_eq⟩
      rw [Finset.sum_eq_zero fun ν _ => ?_, eq_comm, Nat.card_eq_zero]
      · exact Or.inl hempty
      · split_ifs with heq
        · exfalso; exact hcard (by rw [(hw_iff ν).mp heq, YoungDiagram.card_ofPartition])
        · rfl
  · refine Finset.sum_eq_zero fun ν _ => ?_
    split_ifs with heq
    · exact absurd (detShift_le_of_eq_shift_weightOfShape heq) hshift
    · rfl

/-- **Commutativity of Littlewood–Richardson hive counts**:
`hiveCount (productBoundary λ μ γ) = hiveCount (productBoundary μ λ γ)`. -/
theorem hiveCount_comm {n : ℕ} (lam μ γ : DominantWeight n) :
    hiveCount (productBoundary lam μ γ) = hiveCount (productBoundary μ lam γ) := by
  rw [← finrank_hom_eq_hiveCount, ← finrank_hom_eq_hiveCount]
  let e₁ := (FDRep.forget₂HomLinearEquiv (rationalWeylFDRep ℂ n γ)
    (rationalWeylFDRep ℂ n lam ⊗ rationalWeylFDRep ℂ n μ)).symm ≪≫ₗ Rep.homLinearEquiv _ _
  let e₂ := Representation.Equiv.intertwiningMapCongr
    (Representation.Equiv.refl (rationalWeylRep ℂ n γ))
    (Representation.TensorProduct.comm (rationalWeylRep ℂ n lam) (rationalWeylRep ℂ n μ))
  let e₃ := ((FDRep.forget₂HomLinearEquiv (rationalWeylFDRep ℂ n γ)
    (rationalWeylFDRep ℂ n μ ⊗ rationalWeylFDRep ℂ n lam)).symm ≪≫ₗ Rep.homLinearEquiv _ _).symm
  exact (e₁ ≪≫ₗ e₂ ≪≫ₗ e₃).finrank_eq

end TensorMultiplicities

/-! ### Concrete checks at ranks `0`, `1`, `2` (signed), and `3` (multiplicity `2`) -/

section ConcreteChecks

/-- Rank-`0` check: the unique trivial representation has tensor multiplicity `1`. -/
theorem finrank_hom_zero_eq_one (lam μ γ : DominantWeight 0) :
    Module.finrank ℂ
        (rationalWeylFDRep ℂ 0 γ ⟶ rationalWeylFDRep ℂ 0 lam ⊗ rationalWeylFDRep ℂ 0 μ) = 1 := by
  rw [finrank_hom_eq_hiveCount, hiveCount_rank_zero]

/-- Rank-`1` check: `hiveCount` for `GL₁` characters is `1` when `λ₀ + μ₀ = γ₀` and `0`
otherwise. -/
theorem hiveCount_one_productBoundary (lam μ γ : DominantWeight 1) :
    hiveCount (productBoundary lam μ γ) = if lam.1 0 + μ.1 0 = γ.1 0 then 1 else 0 := by
  split_ifs with hsum
  · have : Unique (FixedIntegerHive (productBoundary lam μ γ)) :=
      { default := ⟨equivOne.symm (lam.1 0, γ.1 0), by
          ext s i; fin_cases i; fin_cases s <;> simp; omega⟩
        uniq := fun h => Subtype.ext <| equivOne.injective <| Prod.ext
          (by
            have hb := congrFun (congrFun h.2 0) 0
            rw [boundary_apply, productBoundary_zero] at hb
            have h0 : Vertex.edgePoint 1 0 (0 : Fin 1).castSucc = Vertex.cornerA 1 := by
              ext <;> simp
            have h1 : Vertex.edgePoint 1 0 (0 : Fin 1).succ = ⟨0, 1, 0, rfl⟩ := by
              ext <;> simp
            rw [h0, h1, h.1.apply_cornerA, sub_zero] at hb
            simpa [equivOne_apply] using hb)
          (by
            have hb := congrFun (congrFun h.2 2) 0
            rw [boundary_apply, productBoundary_two, DominantWeight.dual_apply] at hb
            have h0 : Vertex.edgePoint 1 2 (0 : Fin 1).castSucc = ⟨0, 0, 1, rfl⟩ := by
              ext <;> simp
            have h1 : Vertex.edgePoint 1 2 (0 : Fin 1).succ = Vertex.cornerA 1 := by
              ext <;> simp
            rw [h0, h1, h.1.apply_cornerA, zero_sub, Fin.rev_zero] at hb
            simpa [equivOne_apply] using neg_inj.mp hb) }
    rw [← card_fixedIntegerHive]
    exact Fintype.card_unique
  · exact hiveCount_eq_zero_iff.mpr ⟨fun ⟨_, hb⟩ => hsum (by
      simpa using sum_eq_of_productBoundary hb)⟩

/-- Rank-`1` `GL₁(ℂ)` tensor-product check via `finrank_hom_eq_hiveCount`. -/
theorem finrank_hom_one_eq_ite (lam μ γ : DominantWeight 1) :
    Module.finrank ℂ
        (rationalWeylFDRep ℂ 1 γ ⟶ rationalWeylFDRep ℂ 1 lam ⊗ rationalWeylFDRep ℂ 1 μ) =
      if lam.1 0 + μ.1 0 = γ.1 0 then 1 else 0 := by
  rw [finrank_hom_eq_hiveCount, hiveCount_one_productBoundary]

/-- Rank-`2` signed check: `V_{(1, 0)} ⊗ V_{(0, -1)}` contains the trivial module `V_{(0, 0)}` with
multiplicity `1`, reduced by a determinant shift to `c^{(1, 1)}_{(1, 0), (1, 0)} = 1`. -/
theorem hiveCount_two_std_dual_trivial :
    hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![0, -1], by decide⟩ ⟨![0, 0], by decide⟩) = 1 := by
  rw [← hiveCount_productBoundary_shift _ _ _ 0 1]
  convert hiveCount_two_std_std_det using 2
  ext s i; fin_cases s <;> fin_cases i <;> simp [DominantWeight.dual_apply]

/-- Rank-`2` signed check: `V_{(1, 0)} ⊗ V_{(0, -1)}` contains the adjoint summand `V_{(1, -1)}`
with multiplicity `1`, reduced by a determinant shift to `c^{(2, 0)}_{(1, 0), (1, 0)} = 1`. -/
theorem hiveCount_two_std_dual_adjoint :
    hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![0, -1], by decide⟩ ⟨![1, -1], by decide⟩) = 1 := by
  rw [← hiveCount_productBoundary_shift _ _ _ 0 1]
  convert hiveCount_two_std_std_sym using 2
  ext s i; fin_cases s <;> fin_cases i <;> simp [DominantWeight.dual_apply]

/-- Rank-`2` signed exclusion check: `γ = (2, -2)` violates `λ₂ + μ₂ ≤ γ₂` (`-1 ≤ -2`). -/
theorem hiveCount_two_std_dual_excluded :
    hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![0, -1], by decide⟩ ⟨![2, -2], by decide⟩) = 0 := by
  rw [hiveCount_eq_zero_iff]
  refine ⟨fun ⟨_, hb⟩ => ?_⟩
  have hlast := last_le_of_productBoundary hb
  simp at hlast

/-- On `Δ₃`, the boundary determines every vertex except the unique interior vertex `(1, 1, 1)`. -/
private theorem eq_of_boundary_eq_of_interior_eq_three {h₁ h₂ : IntegerHive 3}
    (hb : h₁.boundary = h₂.boundary) (hm : h₁ ⟨1, 1, 1, rfl⟩ = h₂ ⟨1, 1, 1, rfl⟩) : h₁ = h₂ := by
  refine Hive.ext fun p => ?_
  have := p.sum_eq
  rcases (by omega : p.z = 0 ∨ p.x = 0 ∨ p.y = 0 ∨ (p.x = 1 ∧ p.y = 1 ∧ p.z = 1)) with
    hz | hx | hy | ⟨hx, hy, hz⟩
  · rw [show p = Vertex.edgePoint 3 0 ⟨p.y, by omega⟩ by ext <;> simp [hz]; omega,
      apply_edgePoint_zero, apply_edgePoint_zero, hb]
  · rw [show p = Vertex.edgePoint 3 1 ⟨p.z, by omega⟩ by ext <;> simp [hx]; omega,
      apply_edgePoint_one, apply_edgePoint_one, hb]
  · rw [show p = Vertex.edgePoint 3 2 ⟨p.x, by omega⟩ by ext <;> simp [hy]; omega,
      apply_edgePoint_two, apply_edgePoint_two, hb]
  · rw [show p = ⟨1, 1, 1, rfl⟩ by ext <;> simp [hx, hy, hz], hm]

private def hiveThreeTwoOneFun (t : ℤ) (p : Vertex 3) : ℤ :=
  match p.z, p.y + p.z with
  | 0, 0 => 0
  | 0, 1 => 2
  | 0, 2 => 3
  | 0, 3 => 3
  | 1, 1 => 3
  | 1, 2 => t
  | 1, 3 => 5
  | 2, 2 => 5
  | 2, 3 => 6
  | 3, 3 => 6
  | _, _ => 0

private theorem isRhombusConcave_hiveThreeTwoOneFun {t : ℤ} (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    IsRhombusConcave (hiveThreeTwoOneFun t) := by
  rw [isRhombusConcave_iff_ofIJ]
  refine ⟨fun i j hij hjn => ?_, fun i j hij hjn => ?_, fun i j hij hjn => ?_⟩
  · have : (i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 1) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hiveThreeTwoOneFun] <;> omega
  · have : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hiveThreeTwoOneFun] <;> omega
  · have : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hiveThreeTwoOneFun] <;> omega

private theorem boundary_hiveThreeTwoOneFun {t : ℤ} (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    (Hive.mk (hiveThreeTwoOneFun t) (by simp [hiveThreeTwoOneFun])
      (fun hr => (isRhombusConcave_def _).mp
        (isRhombusConcave_hiveThreeTwoOneFun ht4 ht5) hr)).boundary =
      productBoundary ⟨![2, 1, 0], by decide⟩ ⟨![2, 1, 0], by decide⟩
        ⟨![3, 2, 1], by decide⟩ := by
  ext s i; fin_cases s <;> fin_cases i <;>
    simp [boundary_apply, DominantWeight.dual_apply, hiveThreeTwoOneFun]

/-- Parameterized family of size-`3` hives with boundary `((2, 1, 0), (2, 1, 0), (3, 2, 1)*)` and
interior entry `t ∈ {4, 5}` at `(1, 1, 1)`. -/
private def hiveThreeTwoOne (t : ℤ) (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    FixedIntegerHive
      (productBoundary ⟨![2, 1, 0], by decide⟩ ⟨![2, 1, 0], by decide⟩
        ⟨![3, 2, 1], by decide⟩) :=
  ⟨⟨hiveThreeTwoOneFun t, by simp [hiveThreeTwoOneFun],
      fun hr => (isRhombusConcave_def _).mp (isRhombusConcave_hiveThreeTwoOneFun ht4 ht5) hr⟩,
    boundary_hiveThreeTwoOneFun ht4 ht5⟩

private theorem hiveThreeTwoOne_interior (t : ℤ) (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    (hiveThreeTwoOne t ht4 ht5).1 ⟨1, 1, 1, rfl⟩ = t := rfl

/-- **First multiplicity-`2` check**: `c^{(3, 2, 1)}_{(2, 1, 0), (2, 1, 0)} = 2`, realized by the
two integer hives with interior values `4` and `5` at `(1, 1, 1)`. -/
theorem hiveCount_three_two_one_two_one_three_two_one :
    hiveCount
      (productBoundary ⟨![2, 1, 0], by decide⟩ ⟨![2, 1, 0], by decide⟩
        ⟨![3, 2, 1], by decide⟩) = 2 := by
  let B := productBoundary ⟨![2, 1, 0], by decide⟩ ⟨![2, 1, 0], by decide⟩
    ⟨![3, 2, 1], by decide⟩
  have hbound : ∀ h : FixedIntegerHive B,
      h.1 ⟨1, 1, 1, rfl⟩ = 4 ∨ h.1 ⟨1, 1, 1, rfl⟩ = 5 := fun h => by
    have hu1 := h.1.le_ofIJ_upright (i := 0) (j := 1) (by omega) (by omega)
    have hu2 := h.1.le_ofIJ_upright (i := 0) (j := 2) (by omega) (by omega)
    have h01 : h.1 (Vertex.ofIJ 3 0 1 (by omega) (by omega)) = 2 := by
      rw [Vertex.ofIJ_zero_left, apply_edgePoint_zero, h.2]
      simp [B, Finset.sum_filter]
    have h02 : h.1 (Vertex.ofIJ 3 0 2 (by omega) (by omega)) = 3 := by
      rw [Vertex.ofIJ_zero_left, apply_edgePoint_zero, h.2]
      simp [B, Finset.sum_filter, Fin.sum_univ_three]
    have h03 : h.1 (Vertex.ofIJ 3 0 3 (by omega) (by omega)) = 3 := by
      rw [Vertex.ofIJ_zero_left, apply_edgePoint_zero, h.2]
      simp [B, Fin.sum_univ_three]
    have h11 : h.1 (Vertex.ofIJ 3 1 1 (by omega) (by omega)) = 3 := by
      rw [Vertex.ofIJ_diag, apply_edgePoint_two, h.2]
      simp [B, Finset.sum_filter, Fin.sum_univ_three, DominantWeight.dual_apply]
    have h13 : h.1 (Vertex.ofIJ 3 1 3 (by omega) (by omega)) = 5 := by
      rw [Vertex.ofIJ_right_eq, apply_edgePoint_one, h.2]
      simp [B, Finset.sum_filter, Fin.sum_univ_three]
    have hm : Vertex.ofIJ 3 1 2 (by omega) (by omega) = ⟨1, 1, 1, rfl⟩ := by ext <;> simp
    rw [h01, h02, h11, hm] at hu1
    rw [h02, h03, h13, hm] at hu2
    omega
  let e : FixedIntegerHive B ≃ Bool :=
    { toFun := fun h => decide (h.1 ⟨1, 1, 1, rfl⟩ = 4)
      invFun := fun b => if b then hiveThreeTwoOne 4 le_rfl (by omega)
        else hiveThreeTwoOne 5 (by omega) le_rfl
      left_inv := fun h => Subtype.ext <| by
        rcases hbound h with h4 | h5
        · simp only [h4, decide_true, ↓reduceIte]
          exact eq_of_boundary_eq_of_interior_eq_three
            ((hiveThreeTwoOne 4 le_rfl (by omega)).2.trans h.2.symm)
            (by rw [hiveThreeTwoOne_interior, h4])
        · simp only [h5, show (5 : ℤ) ≠ 4 by omega, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact eq_of_boundary_eq_of_interior_eq_three
            ((hiveThreeTwoOne 5 (by omega) le_rfl).2.trans h.2.symm)
            (by rw [hiveThreeTwoOne_interior, h5])
      right_inv := fun b => by cases b <;> simp [hiveThreeTwoOne_interior] }
  rw [← card_fixedIntegerHive, Fintype.card_congr e, Fintype.card_bool]

/-- `GL₃(ℂ)` multiplicity-`2` check: `V_{(2, 1, 0)} ⊗ V_{(2, 1, 0)}` contains two copies of
`V_{(3, 2, 1)}`. -/
theorem finrank_hom_three_two_one_two_one_three_two_one :
    Module.finrank ℂ
        (rationalWeylFDRep ℂ 3 ⟨![3, 2, 1], by decide⟩ ⟶
          rationalWeylFDRep ℂ 3 ⟨![2, 1, 0], by decide⟩ ⊗
            rationalWeylFDRep ℂ 3 ⟨![2, 1, 0], by decide⟩) = 2 := by
  rw [finrank_hom_eq_hiveCount, hiveCount_three_two_one_two_one_three_two_one]

end ConcreteChecks

end TauCeti.Hive
