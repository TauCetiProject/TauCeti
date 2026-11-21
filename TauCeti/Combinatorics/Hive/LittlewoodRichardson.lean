/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Fibre
public import TauCeti.Combinatorics.Young.LittlewoodRichardson.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import TauCeti.Combinatorics.Hive.GelfandTsetlin

/-!
# The hive-to-Littlewood–Richardson equivalence

In the **product chart** `Vertex.ofChart n i j` (`0 ≤ i ≤ j ≤ n` mapped to the barycentric
point `(n - j, j - i, i)` of `Δₙ`, defined in `TauCeti.Combinatorics.Hive.Lattice`), the three
perimeter sides align directly with the product boundary `(λ, μ, γ*)`:
* `i = 0` runs clockwise along `A → B`, where successive differences record `λ`;
* `j = n` runs clockwise along `B → C`, where successive differences record `μ`;
* the diagonal `i = j` runs counterclockwise along `A → C` (the reverse of `C → A`), so successive
  diagonal values record prefix sums of `γ`.

Every unit rhombus in `Δₙ` belongs to one of three orientations in `(i, j)` coordinates
(`TauCeti.Hive.isRhombusConcave_iff_ofChart` in `TauCeti.Combinatorics.Hive.Basic`),
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

For arbitrary signed dominant weights `λ, μ, γ : DominantWeight n` and any shift pair `(a, b)`
making `λ.shift a`, `μ.shift b`, and `γ.shift (a + b)` polynomial, composing the affine shift
bijection `TauCeti.Hive.fixedIntegerHiveShiftEquiv` (defined in `TauCeti.Combinatorics.Hive.Fibre`)
with `fixedIntegerHiveEquivLRTableau` yields an explicit bijection with
`LRTableau (λ.shift a).shape (γ.shift (a + b)).shape (μ.shift b).shape`
(`TauCeti.Hive.fixedIntegerHiveShiftEquivLRTableau`), specializing at `(-λ.detShift, -μ.detShift)`
to `LRTableau λ.detShiftShape (γ.shift (-(λ.detShift + μ.detShift))).shape μ.detShiftShape`
whenever `λ.detShift + μ.detShift ≤ γ.detShift`
(`TauCeti.Hive.fixedIntegerHiveSignedEquivLRTableau`). Any two admissible shift pairs induce
canonically equivalent tableau carriers (`TauCeti.Hive.lrTableauShiftEquiv`).

## Main definitions

* `TauCeti.Hive.hiveOfLRTableau` and `TauCeti.Hive.lrTableauOfHive`: explicit mutually inverse
  constructions between Littlewood–Richardson tableaux and normalized integer hives.
* `TauCeti.Hive.fixedIntegerHiveEquivLRTableau`,
  `TauCeti.Hive.fixedIntegerHiveWeightOfShapeEquivLRTableau`,
  `TauCeti.Hive.fixedIntegerHiveShiftEquivLRTableau`,
  `TauCeti.Hive.lrTableauShiftEquiv`, and `TauCeti.Hive.fixedIntegerHiveSignedEquivLRTableau`:
  the polynomial, Young-diagram, arbitrary-shift, shift-transport, and canonical signed
  hive-to-Littlewood–Richardson equivalences.

## Main results

* `TauCeti.Hive.boundary_hiveOfLRTableau` and `TauCeti.Hive.hiveRowCount_hiveOfLRTableau`:
  boundary and row-count inversion identities for `hiveOfLRTableau`.
* `TauCeti.Hive.rowCount_fixedIntegerHiveWeightOfShapeEquivLRTableau`,
  `TauCeti.Hive.rowCount_fixedIntegerHiveShiftEquivLRTableau`,
  `TauCeti.Hive.rowCount_lrTableauShiftEquiv`, and
  `TauCeti.Hive.rowCount_fixedIntegerHiveSignedEquivLRTableau`: row-count characterizations of the
  Young-diagram, arbitrary-shift, shift-transport, and canonical signed equivalences.

## References

* A. Knutson and T. Tao, *The honeycomb model of GLₙ(ℂ) tensor products I: Proof of the saturation
  conjecture*, J. Amer. Math. Soc. 12 (1999), 1055–1090, Appendix 2.
* A. S. Buch, *The saturation conjecture (after A. Knutson and T. Tao)*, Enseign. Math. (2) 46
  (2000), 43–60, Appendix.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

variable {n : ℕ}

/-! ### Forward map: from a Littlewood–Richardson tableau to an integer hive -/

section ForwardMap

section
variable {inner outer : YoungDiagram} (lam : DominantWeight n)
  (T : SkewSemistandardYoungTableau inner outer)

/-- The lattice function on `Vertex n` attached to a dominant weight `λ` and a skew tableau `T`:
at `ofChart n i j` it sums `λ_r` for `r < j` plus the counts of letters `k < i` in rows
`r < j`. -/
def lrHiveFun (p : Vertex n) : ℤ :=
  TauCeti.prefixSum (p.y + p.z) lam.val +
    ∑ k ∈ Finset.range p.z, ∑ r ∈ Finset.range (p.y + p.z), (T.rowCount r k : ℤ)

theorem lrHiveFun_apply (p : Vertex n) :
    lrHiveFun lam T p = TauCeti.prefixSum (p.y + p.z) lam.val +
      ∑ k ∈ Finset.range p.z, ∑ r ∈ Finset.range (p.y + p.z), (T.rowCount r k : ℤ) := (rfl)

@[simp] theorem lrHiveFun_cornerA : lrHiveFun lam T (Vertex.cornerA n) = 0 := by simp [lrHiveFun]

@[simp] theorem lrHiveFun_ofChart {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    lrHiveFun lam T (Vertex.ofChart n i j hij hj) =
      TauCeti.prefixSum j lam.val +
        ∑ k ∈ Finset.range i, ∑ r ∈ Finset.range j, (T.rowCount r k : ℤ) := by
  simp [lrHiveFun, Nat.sub_add_cancel hij]

/-- Shifting the inner dominant weight `λ` by `a` shifts `lrHiveFun lam T p` by
`((p.y : ℤ) + p.z) * a`. -/
@[simp] theorem lrHiveFun_shift (a : ℤ) (p : Vertex n) :
    lrHiveFun (lam.shift a) T p = lrHiveFun lam T p + ((p.y : ℤ) + p.z) * a := by
  have hsum : TauCeti.prefixSum (p.y + p.z) (fun _ : Fin n => a) = ((p.y : ℤ) + p.z) * a := by
    simpa [min_eq_left (by have := p.sum_eq; omega : p.y + p.z ≤ n)] using
      TauCeti.prefixSum_eq_sum_range (n := n) (p.y + p.z) (fun _ => a)
  have hshift : (lam.shift a).val = lam.val + fun _ => a := rfl
  simp only [lrHiveFun, hshift, TauCeti.prefixSum_add, hsum]; abel

end

/-- Transporting a Littlewood–Richardson tableau along shape equalities does not change
`lrHiveFun`. -/
@[simp] theorem lrHiveFun_congr {inner outer μ inner' outer' μ' : YoungDiagram}
    (lam : DominantWeight n) (hinner : inner = inner') (houter : outer = outer') (hμ : μ = μ')
    (T : LRTableau inner outer μ) (p : Vertex n) :
    lrHiveFun lam (LRTableau.congr hinner houter hμ T).val p = lrHiveFun lam T.val p := by
  simp [lrHiveFun]

/-- On a Littlewood–Richardson tableau, `lrHiveFun` restricts the inner row sum to `k ≤ r < j`:
`h(i, j) = ∑_{r < j} λ_r + ∑_{k < i} ∑_{k ≤ r < j} T.rowCount r k`. -/
theorem lrHiveFun_ofChart_eq_sum_Ico {i j : ℕ} {inner outer μ : YoungDiagram}
    (lam : DominantWeight n) (T : LRTableau inner outer μ) (hij : i ≤ j) (hj : j ≤ n) :
    lrHiveFun lam T.val (Vertex.ofChart n i j hij hj) =
      TauCeti.prefixSum j lam.val +
        ∑ k ∈ Finset.range i, ∑ r ∈ Finset.Ico k j, (T.val.rowCount r k : ℤ) := by
  rw [lrHiveFun_ofChart]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkj : k ≤ j := (Finset.mem_range.mp hk).le.trans hij
  rw [← Finset.sum_range_add_sum_Ico _ hkj,
    Finset.sum_eq_zero fun r hr => by simp [T.rowCount_eq_zero_of_lt (Finset.mem_range.mp hr)],
    zero_add]

private def lrGTPattern {inner outer μ : YoungDiagram} (n : ℕ)
    (T : LRTableau inner outer μ) : GTPattern n where
  entry k j :=
    if k < j then if j ≤ n then ∑ r ∈ Finset.range j, (T.val.rowCount r k : ℤ) else 0 else 0
  zeros' {k j} hout := by rcases hout with hnj | hjk <;> split_ifs <;> omega
  interlacing' {k j} hkj hj := by
    simp only [ite_eq_left hkj, ite_eq_left hj.le, ite_eq_left (by omega : k < j + 1),
      ite_eq_left (Nat.succ_le_of_lt hj), ite_eq_left (Nat.succ_lt_succ hkj)]
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_range_succ]
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    · exact_mod_cast (T.val.isLatticeWord_readingWord_iff.mp T.property.right) k j

private theorem lrGTPattern_apply_of_lt_of_le {inner outer μ : YoungDiagram}
    (T : LRTableau inner outer μ) {k j : ℕ} (hkj : k < j) (hj : j ≤ n) :
    lrGTPattern n T k j = ∑ r ∈ Finset.range j, (T.val.rowCount r k : ℤ) := by
  change (if k < j then if j ≤ n then ∑ r ∈ Finset.range j, (T.val.rowCount r k : ℤ) else 0
    else 0) = _
  rw [ite_eq_left hkj, ite_eq_left hj]

private theorem isGTCompletable_lrGTPattern {outer μ : YoungDiagram} {lam : DominantWeight n}
    (hlam : lam.IsPolynomial) (T : LRTableau lam.shape outer μ) :
    IsGTCompletable lam (lrGTPattern n T) := by
  rw [isGTCompletable_iff_sum_sub_le]
  intro i j hij hj
  have hsub1 : ∀ k ∈ Finset.range (i + 1),
      lrGTPattern n T k (j + 2) - lrGTPattern n T k (j + 1) =
        (T.val.rowCount (j + 1) k : ℤ) := fun k hk => by
    have hki : k < i + 1 := Finset.mem_range.mp hk
    rw [lrGTPattern_apply_of_lt_of_le T (by omega) (by omega),
      lrGTPattern_apply_of_lt_of_le T (by omega) (by omega), Finset.sum_range_succ]
    abel
  have hsub0 : ∀ k ∈ Finset.range i,
      lrGTPattern n T k (j + 1) - lrGTPattern n T k j = (T.val.rowCount j k : ℤ) := fun k hk => by
    have hki : k < i := Finset.mem_range.mp hk
    rw [lrGTPattern_apply_of_lt_of_le T (by omega) (by omega),
      lrGTPattern_apply_of_lt_of_le T (by omega) (by omega), Finset.sum_range_succ]
    abel
  rw [Finset.sum_congr rfl hsub1, Finset.sum_congr rfl hsub0,
    ← DominantWeight.natCast_rowLen_shape hlam ⟨j, by omega⟩,
    ← DominantWeight.natCast_rowLen_shape hlam ⟨j + 1, by omega⟩]
  have hcol : (lam.shape.rowLen (j + 1) : ℤ) +
      ∑ k ∈ Finset.range (i + 1), (T.val.rowCount (j + 1) k : ℤ) ≤
      (lam.shape.rowLen j : ℤ) + ∑ k ∈ Finset.range i, (T.val.rowCount j k : ℤ) := by
    exact_mod_cast T.val.rowLen_add_sum_range_rowCount_succ_le j i
  linarith

private theorem gtCompletion_lrGTPattern {inner outer μ : YoungDiagram} (lam : DominantWeight n)
    (T : LRTableau inner outer μ) (p : Vertex n) :
    gtCompletion lam (lrGTPattern n T) p.z (n - p.x) = lrHiveFun lam T.val p := by
  have hxp := p.sum_eq
  have hpyz : n - p.x = p.y + p.z := by omega
  rw [gtCompletion_def, lrHiveFun_apply, hpyz]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkz : k < p.z := Finset.mem_range.mp hk
  exact lrGTPattern_apply_of_lt_of_le T (by omega) (by omega)

private theorem topRow_lrGTPattern {inner : YoungDiagram} {μ γ : DominantWeight n}
    (hμ : μ.IsPolynomial) (T : LRTableau inner γ.shape μ.shape) :
    (lrGTPattern n T).topRow = μ.val := by
  ext k
  rw [GTPattern.topRow_apply, lrGTPattern_apply_of_lt_of_le T k.isLt le_rfl, ← Nat.cast_sum,
    T.val.sum_range_rowCount_eq_content k (DominantWeight.colLen_zero_shape_le γ),
    congrFun T.property.left k, DominantWeight.natCast_rowLen_shape hμ k]

private theorem rowWeight_lrGTPattern {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) :
    (lrGTPattern n T).rowWeight = γ.val - lam.val := by
  have hrowSum : ∀ j ≤ n, (lrGTPattern n T).rowSum j =
      ∑ s ∈ Finset.range j, ((γ.shape.rowLen s : ℤ) - (lam.shape.rowLen s : ℤ)) := by
    intro j hj
    rw [GTPattern.rowSum_def]
    have h1 : ∀ k ∈ Finset.range j, lrGTPattern n T k j =
        ∑ s ∈ Finset.range j, (T.val.rowCount s k : ℤ) := fun k hk =>
      lrGTPattern_apply_of_lt_of_le T (Finset.mem_range.mp hk) hj
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hsum_nat : ∑ k ∈ Finset.range j, T.val.rowCount s k =
        γ.shape.rowLen s - lam.shape.rowLen s :=
      T.val.sum_range_rowCount_of_forall_lt fun c _ _ =>
        (T.entry_le s c).trans_lt (Finset.mem_range.mp hs)
    have hle_row : lam.shape.rowLen s ≤ γ.shape.rowLen s := YoungDiagram.rowLen_le_of_le T.val.le s
    rw [← Nat.cast_sum, hsum_nat, Nat.cast_sub hle_row]
  ext r
  rw [GTPattern.rowWeight_eq_rowSum_sub, hrowSum (r.val + 1) r.isLt, hrowSum r.val r.isLt.le,
    Finset.sum_range_succ, add_sub_cancel_left, Pi.sub_apply,
    DominantWeight.natCast_rowLen_shape hγ r, DominantWeight.natCast_rowLen_shape hlam r]

/-- Forward construction of an `IntegerHive n` from a polynomial dominant weight `λ` and a
Littlewood–Richardson tableau `T : LRTableau λ.shape outer μ`. -/
def hiveOfLRTableau {outer μ : YoungDiagram} {lam : DominantWeight n}
    (hlam : lam.IsPolynomial) (T : LRTableau lam.shape outer μ) : IntegerHive n :=
  ofGTPattern lam (lrGTPattern n T) (isGTCompletable_lrGTPattern hlam T)

@[simp] theorem hiveOfLRTableau_apply {outer μ : YoungDiagram} {lam : DominantWeight n}
    (hlam : lam.IsPolynomial) (T : LRTableau lam.shape outer μ) (p : Vertex n) :
    hiveOfLRTableau hlam T p = lrHiveFun lam T.val p :=
  (ofGTPattern_apply _ _ _ p).trans (gtCompletion_lrGTPattern lam T p)

theorem hiveOfLRTableau_ofChart {i j : ℕ} {outer μ : YoungDiagram}
    {lam : DominantWeight n} (hlam : lam.IsPolynomial) (T : LRTableau lam.shape outer μ)
    (hij : i ≤ j) (hj : j ≤ n) :
    hiveOfLRTableau hlam T (Vertex.ofChart n i j hij hj) =
      TauCeti.prefixSum j lam.val +
        ∑ k ∈ Finset.range i, ∑ r ∈ Finset.range j, (T.val.rowCount r k : ℤ) := by
  rw [hiveOfLRTableau_apply, lrHiveFun_ofChart]

/-- Along the diagonal `i = j`, `hiveOfLRTableau` records the prefix sums of `γ`. -/
theorem hiveOfLRTableau_ofChart_self {j : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) (hj : j ≤ n) :
    hiveOfLRTableau hlam T (Vertex.ofChart n j j le_rfl hj) =
      TauCeti.prefixSum j γ.val := by
  rw [hiveOfLRTableau, ofGTPattern_ofChart]
  exact gtCompletion_self_of_rowWeight (rowWeight_lrGTPattern hlam hγ T) hj

/-- The clockwise cyclic boundary of `hiveOfLRTableau hlam T` is `productBoundary lam μ γ`. -/
@[simp] theorem boundary_hiveOfLRTableau {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) :
    (hiveOfLRTableau hlam T).boundary = productBoundary lam μ γ :=
  boundary_ofGTPattern_eq_productBoundary (topRow_lrGTPattern hμ T)
    (rowWeight_lrGTPattern hlam hγ T) _

/-- Bundled forward map into `FixedIntegerHive (productBoundary lam μ γ)`. -/
def fixedIntegerHiveOfLRTableau {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) : FixedIntegerHive (productBoundary lam μ γ) :=
  ⟨hiveOfLRTableau hlam T, boundary_hiveOfLRTableau hlam hμ hγ T⟩

@[simp] theorem coe_fixedIntegerHiveOfLRTableau {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) :
    (fixedIntegerHiveOfLRTableau hlam hμ hγ T).val = hiveOfLRTableau hlam T := (rfl)

end ForwardMap

/-! ### Inverse map: row-count extraction and tableau reconstruction from a hive -/

section InverseMap

/-- Signed row-letter count extracted from a hive `h` at skew row `r` and letter `k`:
the vertical difference `h.toGTPattern k (r + 1) - h.toGTPattern k r` for `r < n`, and `0`
otherwise. -/
def hiveRowCountInt (h : Hive n ℤ) (r k : ℕ) : ℤ :=
  if r < n then h.toGTPattern k (r + 1) - h.toGTPattern k r else 0

theorem hiveRowCountInt_of_lt {r k : ℕ} (h : Hive n ℤ) (hkr : k < r) (hr : r < n) :
    hiveRowCountInt h r k =
      h (Vertex.ofChart n (k + 1) (r + 1) (by omega) (by omega)) -
        h (Vertex.ofChart n k (r + 1) (by omega) (by omega)) -
        h (Vertex.ofChart n (k + 1) r (by omega) (by omega)) +
        h (Vertex.ofChart n k r (by omega) (by omega)) := by
  rw [hiveRowCountInt, ite_eq_left hr,
    h.toGTPattern_apply_of_lt_of_le (by omega) (by omega),
    h.toGTPattern_apply_of_lt_of_le hkr hr.le]
  abel

theorem hiveRowCountInt_diag {r : ℕ} (h : Hive n ℤ) (hr : r < n) :
    hiveRowCountInt h r r =
      h (Vertex.ofChart n (r + 1) (r + 1) le_rfl (by omega)) -
        h (Vertex.ofChart n r (r + 1) (by omega) (by omega)) := by
  rw [hiveRowCountInt, ite_eq_left hr, h.toGTPattern.entry_eq_zero_of_le le_rfl, sub_zero,
    h.toGTPattern_apply_of_lt_of_le (Nat.lt_succ_self r) hr]

theorem hiveRowCountInt_eq_zero_of_lt {r k : ℕ} (h : Hive n ℤ) (hrk : r < k) :
    hiveRowCountInt h r k = 0 := by
  unfold hiveRowCountInt
  split_ifs with hr
  · rw [h.toGTPattern.entry_eq_zero_of_le (by omega),
      h.toGTPattern.entry_eq_zero_of_le hrk.le, sub_zero]
  · rfl

theorem hiveRowCountInt_eq_zero_of_le {r k : ℕ} (h : Hive n ℤ) (hnr : n ≤ r) :
    hiveRowCountInt h r k = 0 := by simp [hiveRowCountInt, Nat.not_lt.mpr hnr]

/-- Letters `k ≥ n` never occur in `hiveRowCountInt`. -/
theorem hiveRowCountInt_eq_zero_of_le_letter {r k : ℕ} (h : Hive n ℤ) (hnk : n ≤ k) :
    hiveRowCountInt h r k = 0 := by
  by_cases hr : r < n
  · exact hiveRowCountInt_eq_zero_of_lt h (lt_of_lt_of_le hr hnk)
  · exact hiveRowCountInt_eq_zero_of_le h (Nat.le_of_not_lt hr)

@[simp] theorem hiveRowCountInt_zero (r k : ℕ) :
    hiveRowCountInt (0 : Hive n ℤ) r k = 0 := by simp [hiveRowCountInt]

@[simp] theorem hiveRowCountInt_add (h₁ h₂ : Hive n ℤ) (r k : ℕ) :
    hiveRowCountInt (h₁ + h₂) r k = hiveRowCountInt h₁ r k + hiveRowCountInt h₂ r k := by
  unfold hiveRowCountInt
  simp only [toGTPattern_add, GTPattern.add_apply]
  split_ifs <;> [abel; rfl]

/-- An affine hive `affine n β γ` has zero off-diagonal counts and diagonal counts `γ - β`
for `r < n`. -/
@[simp] theorem hiveRowCountInt_affine (β γ : ℤ) (r k : ℕ) :
    hiveRowCountInt (affine n β γ) r k = if r < n ∧ k = r then γ - β else 0 := by
  rw [hiveRowCountInt, toGTPattern_affine, GTPattern.const_apply, GTPattern.const_apply]
  split_ifs <;> omega

private theorem sum_range_hiveRowCountInt_left_eq_toGTPattern {x : ℕ} (h : Hive n ℤ) (k : ℕ)
    (hx : x ≤ n) : ∑ r ∈ Finset.range x, hiveRowCountInt h r k = h.toGTPattern k x := by
  rw [Finset.sum_congr rfl fun r hr => by
      rw [hiveRowCountInt, ite_eq_left ((Finset.mem_range.mp hr).trans_le hx)],
    Finset.sum_range_sub (fun r => h.toGTPattern k r) x,
    h.toGTPattern.entry_eq_zero_of_le (Nat.zero_le k), sub_zero]

/-- **Column telescoping of `hiveRowCountInt`**: summing letter `k` across rows `r < x` (`x ≤ n`)
gives `h(k + 1, x) - h(k, x)` when `k < x`, and `0` when `x ≤ k`. -/
theorem sum_range_hiveRowCountInt_left {x : ℕ} (h : Hive n ℤ) (k : ℕ) (hx : x ≤ n) :
    ∑ r ∈ Finset.range x, hiveRowCountInt h r k =
      if hkx : k < x then
        h (Vertex.ofChart n (k + 1) x hkx hx) -
          h (Vertex.ofChart n k x (Nat.le_of_lt hkx) hx)
      else 0 := by
  rw [sum_range_hiveRowCountInt_left_eq_toGTPattern h k hx]
  split_ifs with hkx
  · exact h.toGTPattern_apply_of_lt_of_le hkx hx
  · exact h.toGTPattern.entry_eq_zero_of_le (Nat.not_lt.mp hkx)

/-- **Double telescoping of `hiveRowCountInt`**: summing `hiveRowCountInt h r k` over `k < i` and
`r < j` (`0 ≤ i ≤ j ≤ n`) recovers `h(i, j) - h(0, j)`. -/
theorem sum_range_sum_range_hiveRowCountInt {i j : ℕ} (h : Hive n ℤ) (hij : i ≤ j) (hj : j ≤ n) :
    ∑ k ∈ Finset.range i, ∑ r ∈ Finset.range j, hiveRowCountInt h r k =
      h (Vertex.ofChart n i j hij hj) - h (Vertex.ofChart n 0 j j.zero_le hj) := by
  rw [Finset.sum_congr rfl fun k _ => sum_range_hiveRowCountInt_left_eq_toGTPattern h k hj]
  exact h.sum_range_toGTPattern hij hj

/-- Row-prefix telescoping for `i ≤ r < n`. -/
theorem sum_range_hiveRowCountInt_right {i r : ℕ} (h : Hive n ℤ) (hir : i ≤ r) (hr : r < n) :
    ∑ k ∈ Finset.range i, hiveRowCountInt h r k =
      (h (Vertex.ofChart n i (r + 1) (by omega) (by omega)) -
          h (Vertex.ofChart n i r hir (by omega))) -
        (h (Vertex.ofChart n 0 (r + 1) (Nat.zero_le _) (by omega)) -
          h (Vertex.ofChart n 0 r (Nat.zero_le _) (by omega))) := by
  rw [Finset.sum_congr rfl fun k _ => by rw [hiveRowCountInt, ite_eq_left hr],
    Finset.sum_sub_distrib, h.sum_range_toGTPattern (by omega) hr,
    h.sum_range_toGTPattern hir hr.le]
  abel

/-- Full-row telescoping across `k < m` (`r < m`) for `r < n`. -/
theorem sum_range_hiveRowCountInt_right_of_lt {r m : ℕ} (h : Hive n ℤ) (hr : r < n) (hrm : r < m) :
    ∑ k ∈ Finset.range m, hiveRowCountInt h r k =
      (h (Vertex.ofChart n (r + 1) (r + 1) le_rfl (by omega)) -
          h (Vertex.ofChart n r r le_rfl (by omega))) -
        (h (Vertex.ofChart n 0 (r + 1) (Nat.zero_le _) (by omega)) -
          h (Vertex.ofChart n 0 r (Nat.zero_le _) (by omega))) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hrm)
  have htail : ∑ x ∈ Finset.range d, hiveRowCountInt h r (r + 1 + x) = 0 :=
    Finset.sum_eq_zero fun x _ => hiveRowCountInt_eq_zero_of_lt h (by omega)
  rw [Finset.sum_range_add, htail, add_zero, Finset.sum_range_succ,
    sum_range_hiveRowCountInt_right h le_rfl hr, hiveRowCountInt_diag h hr]; abel

/-- On any integer hive, the diagonal counts `hiveRowCountInt h r r` decrease weakly in `r < n`. -/
theorem hiveRowCountInt_diag_anti {r₁ r₂ : ℕ} (h : Hive n ℤ) (hr₁₂ : r₁ ≤ r₂) (hr₂ : r₂ < n) :
    hiveRowCountInt h r₂ r₂ ≤ hiveRowCountInt h r₁ r₁ := by
  rw [hiveRowCountInt, ite_eq_left hr₂, hiveRowCountInt, ite_eq_left (hr₁₂.trans_lt hr₂),
    h.toGTPattern.entry_eq_zero_of_le le_rfl, h.toGTPattern.entry_eq_zero_of_le le_rfl,
    sub_zero, sub_zero]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hr₁₂
  have hle := h.toGTPattern.entry_add_le (i := r₁) (j := r₁ + 1) (d := d) (by omega)
  have h1 : r₁ + d = r₂ := by omega
  have h2 : r₁ + 1 + d = r₂ + 1 := by omega
  rwa [h1, h2] at hle

/-- **Nonnegativity of all extracted counts (including the diagonal)** when `h` has boundary
`productBoundary lam μ γ` and `μ` is polynomial. -/
theorem hiveRowCountInt_nonneg_of_productBoundary {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hμ : μ.IsPolynomial) (r k : ℕ) :
    0 ≤ hiveRowCountInt h r k := by
  by_cases hr : r < n
  · rcases lt_trichotomy k r with hkr | rfl | hrk
    · rw [hiveRowCountInt, ite_eq_left hr, sub_nonneg]
      exact h.toGTPattern.entry_le_entry_succ_row hkr hr
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine le_trans ?_ (hiveRowCountInt_diag_anti h (r₁ := k) (r₂ := m)
        (by omega) (Nat.lt_succ_self m))
      rw [hiveRowCountInt, ite_eq_left (Nat.lt_succ_self m),
        h.toGTPattern.entry_eq_zero_of_le le_rfl,
        sub_zero, ← GTPattern.topRow_apply _ ⟨m, Nat.lt_succ_self m⟩,
        topRow_toGTPattern_of_productBoundary hb]
      exact (DominantWeight.isPolynomial_def μ).mp hμ ⟨m, Nat.lt_succ_self m⟩
    · rw [hiveRowCountInt_eq_zero_of_lt h hrk]
  · rw [hiveRowCountInt_eq_zero_of_le h (Nat.le_of_not_lt hr)]

/-- Natural-number row-letter count `a(r, k)` extracted from an integer hive `h`. -/
def hiveRowCount (h : IntegerHive n) (r k : ℕ) : ℕ := (hiveRowCountInt h r k).toNat

theorem hiveRowCount_def (h : IntegerHive n) (r k : ℕ) :
    hiveRowCount h r k = (hiveRowCountInt h r k).toNat := (rfl)

/-- On an integer hive with boundary `productBoundary lam μ γ` and polynomial `μ`, casting
`hiveRowCount h r k` back to `ℤ` recovers `hiveRowCountInt h r k`. -/
theorem natCast_hiveRowCount_of_productBoundary {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hμ : μ.IsPolynomial) (r k : ℕ) :
    (hiveRowCount h r k : ℤ) = hiveRowCountInt h r k :=
  Int.toNat_of_nonneg (hiveRowCountInt_nonneg_of_productBoundary hb hμ r k)

theorem hiveRowCount_eq_zero_of_lt {r k : ℕ} (h : IntegerHive n) (hrk : r < k) :
    hiveRowCount h r k = 0 := by simp [hiveRowCount, hiveRowCountInt_eq_zero_of_lt h hrk]

theorem hiveRowCount_eq_zero_of_le {r k : ℕ} (h : IntegerHive n) (hnr : n ≤ r) :
    hiveRowCount h r k = 0 := by simp [hiveRowCount, hiveRowCountInt_eq_zero_of_le h hnr]

/-- Letters `k ≥ n` never occur in `hiveRowCount`. -/
theorem hiveRowCount_eq_zero_of_le_letter {r k : ℕ} (h : IntegerHive n) (hnk : n ≤ k) :
    hiveRowCount h r k = 0 := by simp [hiveRowCount, hiveRowCountInt_eq_zero_of_le_letter h hnk]

@[simp] theorem hiveRowCount_zero (r k : ℕ) : hiveRowCount (0 : IntegerHive n) r k = 0 := by
  simp [hiveRowCount]

/-- Adding `affine n β γ` leaves off-diagonal `hiveRowCount` entries unchanged and shifts diagonal
counts (`r < n`) by `γ - β` before truncation to `ℕ`. -/
@[simp] theorem hiveRowCount_add_affine (h : IntegerHive n) (β γ : ℤ) (r k : ℕ) :
    hiveRowCount (h + affine n β γ) r k =
      if r < n ∧ k = r then (hiveRowCountInt h r r + (γ - β)).toNat else hiveRowCount h r k := by
  by_cases hcond : r < n ∧ k = r
  · rcases hcond with ⟨hr, rfl⟩; simp [hiveRowCount, hr]
  · simp [hiveRowCount, hcond]

/-- Adding an affine hive does not change off-diagonal `hiveRowCount` entries. -/
theorem hiveRowCount_add_affine_of_ne (h : IntegerHive n) (β γ : ℤ) {r k : ℕ} (hne : k ≠ r) :
    hiveRowCount (h + affine n β γ) r k = hiveRowCount h r k := by simp [hne]

/-- Extracting `hiveRowCountInt` from `hiveOfLRTableau hlam T` recovers `(T.val.rowCount r k : ℤ)`
whenever `outer.colLen 0 ≤ n`. -/
@[simp] theorem hiveRowCountInt_hiveOfLRTableau {outer μ : YoungDiagram} {lam : DominantWeight n}
    (hlam : lam.IsPolynomial) (houter : outer.colLen 0 ≤ n) (T : LRTableau lam.shape outer μ)
    (r k : ℕ) : hiveRowCountInt (hiveOfLRTableau hlam T) r k = (T.val.rowCount r k : ℤ) := by
  by_cases hr : r < n
  · rw [hiveRowCountInt, ite_eq_left hr, hiveOfLRTableau, toGTPattern_ofGTPattern]
    rcases lt_trichotomy k r with hkr | rfl | hrk
    · rw [lrGTPattern_apply_of_lt_of_le T (by omega) hr,
        lrGTPattern_apply_of_lt_of_le T hkr hr.le, Finset.sum_range_succ]
      abel
    · rw [lrGTPattern_apply_of_lt_of_le T (Nat.lt_succ_self k) hr,
        (lrGTPattern n T).entry_eq_zero_of_le le_rfl, sub_zero, Finset.sum_range_succ,
        Finset.sum_eq_zero fun s hs => by
          rw [T.rowCount_eq_zero_of_lt (Finset.mem_range.mp hs), Nat.cast_zero],
        zero_add]
    · rw [T.rowCount_eq_zero_of_lt hrk, Nat.cast_zero,
        (lrGTPattern n T).entry_eq_zero_of_le (by omega),
        (lrGTPattern n T).entry_eq_zero_of_le hrk.le, sub_zero]
  · have hnr : n ≤ r := Nat.le_of_not_lt hr
    rw [hiveRowCountInt_eq_zero_of_le _ hnr, T.val.rowCount_eq_zero_of_colLen_le (houter.trans hnr),
      Nat.cast_zero]

/-- Extracting `hiveRowCount` from `hiveOfLRTableau hlam T` recovers `T.val.rowCount` whenever
`outer.colLen 0 ≤ n`. -/
@[simp] theorem hiveRowCount_hiveOfLRTableau {outer μ : YoungDiagram} {lam : DominantWeight n}
    (hlam : lam.IsPolynomial) (houter : outer.colLen 0 ≤ n) (T : LRTableau lam.shape outer μ)
    (r k : ℕ) : hiveRowCount (hiveOfLRTableau hlam T) r k = T.val.rowCount r k := by
  rw [hiveRowCount, hiveRowCountInt_hiveOfLRTableau hlam houter, Int.toNat_natCast]

section
variable {lam μ γ : DominantWeight n} {h : IntegerHive n}
  (hb : h.boundary = productBoundary lam μ γ)
include hb

private theorem sum_range_hiveRowCountInt_right_of_productBoundary {r m : ℕ}
    (hr : r < n) (hrm : r < m) :
    ∑ k ∈ Finset.range m, hiveRowCountInt h r k = γ.val ⟨r, hr⟩ - lam.val ⟨r, hr⟩ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hrm)
  have htail : ∑ x ∈ Finset.range d, hiveRowCountInt h r (r + 1 + x) = 0 :=
    Finset.sum_eq_zero fun x _ => hiveRowCountInt_eq_zero_of_lt h (by omega)
  rw [Finset.sum_range_add, htail, add_zero,
    Finset.sum_congr rfl fun k _ => by rw [hiveRowCountInt, ite_eq_left hr],
    Finset.sum_sub_distrib, Finset.sum_range_succ (n := r) (f := fun k => h.toGTPattern k r),
    h.toGTPattern.entry_eq_zero_of_le le_rfl, add_zero, ← GTPattern.rowWeight_apply _ ⟨r, hr⟩,
    rowWeight_toGTPattern_of_productBoundary hb, Pi.sub_apply]

/-- If an integer hive has polynomial boundary `(λ, μ, γ*)`, then `λ.shape ≤ γ.shape`. -/
theorem shape_le_of_productBoundary (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (hγ : γ.IsPolynomial) : lam.shape ≤ γ.shape := by
  refine YoungDiagram.le_of_forall_rowLen_le fun r => ?_
  by_cases hr : r < n
  · have hfull := sum_range_hiveRowCountInt_right_of_productBoundary hb hr (Nat.lt_succ_self r)
    have hnn : 0 ≤ ∑ k ∈ Finset.range (r + 1), hiveRowCountInt h r k :=
      Finset.sum_nonneg fun k _ => hiveRowCountInt_nonneg_of_productBoundary hb hμ r k
    exact Int.ofNat_le.mp (by
      rw [DominantWeight.natCast_rowLen_shape hlam ⟨r, hr⟩,
        DominantWeight.natCast_rowLen_shape hγ ⟨r, hr⟩]; linarith)
  · simp [DominantWeight.rowLen_shape_eq_zero_of_le _ (Nat.le_of_not_lt hr)]

/-- Row sum of extracted row counts across `k < m` (`r < m` or `n ≤ m`) equals the skew row length
`γ.shape.rowLen r - λ.shape.rowLen r`. -/
theorem sum_range_hiveRowCount_right_of_productBoundary (hlam : lam.IsPolynomial)
    (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial) {r m : ℕ} (hrm : r < m ∨ n ≤ m) :
    ∑ k ∈ Finset.range m, hiveRowCount h r k = γ.shape.rowLen r - lam.shape.rowLen r := by
  by_cases hr : r < n
  · have hfull := sum_range_hiveRowCountInt_right_of_productBoundary hb hr (by omega : r < m)
    rw [← DominantWeight.natCast_rowLen_shape hγ ⟨r, hr⟩,
      ← DominantWeight.natCast_rowLen_shape hlam ⟨r, hr⟩] at hfull
    have hle := YoungDiagram.rowLen_le_of_le (shape_le_of_productBoundary hb hlam hμ hγ) r
    exact Int.ofNat_inj.mp (by
      simp only [Nat.cast_sub hle, Nat.cast_sum, natCast_hiveRowCount_of_productBoundary hb hμ]
      linarith)
  · have hnr : n ≤ r := Nat.le_of_not_lt hr
    simp [hiveRowCount_eq_zero_of_le h hnr, DominantWeight.rowLen_shape_eq_zero_of_le _ hnr]

/-- Column sum of extracted row counts across `r < m` (`n ≤ m`) equals the content row length
`μ.shape.rowLen k`. -/
theorem sum_range_hiveRowCount_left_of_productBoundary {m : ℕ} (hμ : μ.IsPolynomial) (k : ℕ)
    (hm : n ≤ m) : ∑ r ∈ Finset.range m, hiveRowCount h r k = μ.shape.rowLen k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have htail : ∑ r ∈ Finset.range d, hiveRowCount h (n + r) k = 0 :=
    Finset.sum_eq_zero fun r _ => hiveRowCount_eq_zero_of_le h (by omega)
  rw [Finset.sum_range_add, htail, add_zero]
  by_cases hk : k < n
  · have hs := sum_range_hiveRowCountInt_left_eq_toGTPattern h k le_rfl
    rw [← GTPattern.topRow_apply _ ⟨k, hk⟩, topRow_toGTPattern_of_productBoundary hb,
      ← DominantWeight.natCast_rowLen_shape hμ ⟨k, hk⟩] at hs
    exact Int.ofNat_inj.mp (by
      simp only [Nat.cast_sum, natCast_hiveRowCount_of_productBoundary hb hμ]; linarith)
  · rw [DominantWeight.rowLen_shape_eq_zero_of_le μ (Nat.le_of_not_lt hk)]
    exact Finset.sum_eq_zero fun _ _ => hiveRowCount_eq_zero_of_le_letter h (Nat.le_of_not_lt hk)

/-- **Column-strictness inequalities** for the row counts extracted from a hive with polynomial
boundary `productBoundary lam μ γ`. -/
theorem col_strict_hiveRowCount_of_productBoundary (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial)
    (hγ : γ.IsPolynomial) (r x : ℕ) :
    lam.shape.rowLen (r + 1) + ∑ k ∈ Finset.range (x + 1), hiveRowCount h (r + 1) k ≤
      lam.shape.rowLen r + ∑ k ∈ Finset.range x, hiveRowCount h r k := by
  by_cases hr1 : r + 1 < n
  · have hr : r < n := by omega
    by_cases hxr : x ≤ r
    · have hcomp : IsGTCompletable lam h.toGTPattern := by
        have hb0 : h.boundaryWeight 0 = lam := Subtype.ext (by simp [coe_boundaryWeight, hb])
        exact hb0 ▸ h.isGTCompletable_toGTPattern
      have hc := (isGTCompletable_iff_sum_sub_le lam h.toGTPattern).mp hcomp x r hxr (by omega)
      have hs1 : ∑ k ∈ Finset.range (x + 1), hiveRowCountInt h (r + 1) k =
          ∑ k ∈ Finset.range (x + 1), (h.toGTPattern k (r + 2) - h.toGTPattern k (r + 1)) :=
        Finset.sum_congr rfl fun k _ => by rw [hiveRowCountInt, ite_eq_left hr1]
      have hs0 : ∑ k ∈ Finset.range x, hiveRowCountInt h r k =
          ∑ k ∈ Finset.range x, (h.toGTPattern k (r + 1) - h.toGTPattern k r) :=
        Finset.sum_congr rfl fun k _ => by rw [hiveRowCountInt, ite_eq_left hr]
      rw [← DominantWeight.natCast_rowLen_shape hlam ⟨r, hr⟩,
        ← DominantWeight.natCast_rowLen_shape hlam ⟨r + 1, hr1⟩, ← hs1, ← hs0] at hc
      exact Int.ofNat_le.mp (by
        simp only [Nat.cast_add, Nat.cast_sum, natCast_hiveRowCount_of_productBoundary hb hμ]
        linarith)
    · rw [sum_range_hiveRowCount_right_of_productBoundary hb hlam hμ hγ (Or.inl (by omega)),
        sum_range_hiveRowCount_right_of_productBoundary hb hlam hμ hγ (Or.inl (by omega))]
      have hle := YoungDiagram.rowLen_le_of_le (shape_le_of_productBoundary hb hlam hμ hγ)
      have := γ.shape.rowLen_anti r (r + 1) (Nat.le_succ r)
      have := hle r; have := hle (r + 1); omega
  · have hnr : n ≤ r + 1 := Nat.le_of_not_lt hr1
    simp [DominantWeight.rowLen_shape_eq_zero_of_le _ hnr, hiveRowCount_eq_zero_of_le h hnr]

/-- **Ballot (Yamanouchi) prefix inequalities** for the row counts extracted from a hive with
boundary `productBoundary lam μ γ` and polynomial `μ`. -/
theorem ballot_hiveRowCount_of_productBoundary (hμ : μ.IsPolynomial) (k x : ℕ) :
    ∑ r ∈ Finset.range (x + 1), hiveRowCount h r (k + 1) ≤
      ∑ r ∈ Finset.range x, hiveRowCount h r k := by
  rcases lt_or_ge x n with hxn | hnx
  · have hs1 := sum_range_hiveRowCountInt_left_eq_toGTPattern h (k + 1) (by omega : x + 1 ≤ n)
    have hs0 := sum_range_hiveRowCountInt_left_eq_toGTPattern h k (by omega : x ≤ n)
    have hinter := h.toGTPattern.entry_succ_succ_le_entry (i := k) hxn
    exact Int.ofNat_le.mp (by
      simp only [Nat.cast_sum, natCast_hiveRowCount_of_productBoundary hb hμ]; linarith)
  · rw [sum_range_hiveRowCount_left_of_productBoundary hb hμ (k + 1) (by omega),
      sum_range_hiveRowCount_left_of_productBoundary hb hμ k hnx]
    exact μ.shape.rowLen_anti k (k + 1) (Nat.le_succ k)

end

section
variable {lam μ γ : DominantWeight n}
  (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
include hlam hμ hγ

private def lrSkewTableauOfHive (h : FixedIntegerHive (productBoundary lam μ γ)) :
    SkewSemistandardYoungTableau lam.shape γ.shape :=
  SkewSemistandardYoungTableau.ofRowCount
    (shape_le_of_productBoundary h.property hlam hμ hγ) n (hiveRowCount h.val)
    (fun _ => sum_range_hiveRowCount_right_of_productBoundary h.property hlam hμ hγ (Or.inr le_rfl))
    (col_strict_hiveRowCount_of_productBoundary h.property hlam hμ hγ)

private theorem rowCount_lrSkewTableauOfHive (h : FixedIntegerHive (productBoundary lam μ γ))
    (r k : ℕ) : (lrSkewTableauOfHive hlam hμ hγ h).rowCount r k = hiveRowCount h.val r k :=
  SkewSemistandardYoungTableau.rowCount_ofRowCount _ _ _
    (fun _ _ hnk => hiveRowCount_eq_zero_of_le_letter h.val hnk) r k

/-- Reconstruct the Littlewood–Richardson tableau of shape `γ.shape / λ.shape` and content
`μ.shape` from an integer hive with boundary `productBoundary λ μ γ`. -/
def lrTableauOfHive (h : FixedIntegerHive (productBoundary lam μ γ)) :
    LRTableau lam.shape γ.shape μ.shape :=
  ⟨lrSkewTableauOfHive hlam hμ hγ h,
    funext fun k => by
      rw [← (lrSkewTableauOfHive hlam hμ hγ h).sum_range_rowCount_eq_content k
          (DominantWeight.colLen_zero_shape_le γ),
        Finset.sum_congr rfl fun r _ => rowCount_lrSkewTableauOfHive hlam hμ hγ h r k]
      exact sum_range_hiveRowCount_left_of_productBoundary h.property hμ k le_rfl,
    by rw [(lrSkewTableauOfHive hlam hμ hγ h).isLatticeWord_readingWord_iff]
       intro k x; simp only [rowCount_lrSkewTableauOfHive]
       exact ballot_hiveRowCount_of_productBoundary h.property hμ k x⟩

@[simp] theorem rowCount_lrTableauOfHive (h : FixedIntegerHive (productBoundary lam μ γ))
    (r k : ℕ) : (lrTableauOfHive hlam hμ hγ h).val.rowCount r k = hiveRowCount h.val r k :=
  rowCount_lrSkewTableauOfHive hlam hμ hγ h r k

/-- **The hive-to-Littlewood–Richardson equivalence** for polynomial dominant weights `λ, μ, γ`:
an explicit bijection between normalized integer hives with clockwise boundary `(λ, μ, γ*)` and
Littlewood–Richardson tableaux of shape `γ.shape / λ.shape` and content `μ.shape`. -/
def fixedIntegerHiveEquivLRTableau :
    FixedIntegerHive (productBoundary lam μ γ) ≃ LRTableau lam.shape γ.shape μ.shape where
  toFun := lrTableauOfHive hlam hμ hγ
  invFun := fixedIntegerHiveOfLRTableau hlam hμ hγ
  left_inv h := by
    apply Subtype.ext; ext p
    rw [coe_fixedIntegerHiveOfLRTableau, hiveOfLRTableau_apply, ← gtCompletion_lrGTPattern]
    have hP : lrGTPattern n (lrTableauOfHive hlam hμ hγ h) = h.val.toGTPattern := by
      ext k j
      by_cases hkj : k < j ∧ j ≤ n
      · rw [lrGTPattern_apply_of_lt_of_le _ hkj.1 hkj.2]
        simp only [rowCount_lrTableauOfHive, natCast_hiveRowCount_of_productBoundary h.property hμ]
        exact sum_range_hiveRowCountInt_left_eq_toGTPattern h.val k hkj.2
      · exact (GTPattern.entry_eq_zero _ (by omega)).trans
          (h.val.toGTPattern.entry_eq_zero (by omega)).symm
    rw [hP, ← apply_eq_gtCompletion_of_productBoundary h.property p]
  right_inv T := Subtype.ext (SkewSemistandardYoungTableau.eq_of_rowCount_eq fun r k => by
    rw [rowCount_lrTableauOfHive, coe_fixedIntegerHiveOfLRTableau,
      hiveRowCount_hiveOfLRTableau hlam (DominantWeight.colLen_zero_shape_le γ) T])

@[simp] theorem fixedIntegerHiveEquivLRTableau_apply
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    fixedIntegerHiveEquivLRTableau hlam hμ hγ h = lrTableauOfHive hlam hμ hγ h := (rfl)

@[simp] theorem fixedIntegerHiveEquivLRTableau_symm_apply
    (T : LRTableau lam.shape γ.shape μ.shape) :
    (fixedIntegerHiveEquivLRTableau hlam hμ hγ).symm T =
      fixedIntegerHiveOfLRTableau hlam hμ hγ T := (rfl)

end

variable {lam μ ν : YoungDiagram}
  (hlam : lam.colLen 0 ≤ n) (hμ : μ.colLen 0 ≤ n) (hν : ν.colLen 0 ≤ n)
include hlam hμ hν

/-- Young-diagram form of the hive-to-LR equivalence on `weightOfShape n` for diagrams of at most
`n` rows. -/
def fixedIntegerHiveWeightOfShapeEquivLRTableau :
    FixedIntegerHive
      (productBoundary (weightOfShape n lam) (weightOfShape n μ) (weightOfShape n ν)) ≃
      LRTableau lam ν μ :=
  (fixedIntegerHiveEquivLRTableau (isPolynomial_weightOfShape n lam)
    (isPolynomial_weightOfShape n μ) (isPolynomial_weightOfShape n ν)).trans
    (LRTableau.congr (shape_weightOfShape hlam) (shape_weightOfShape hν)
      (shape_weightOfShape hμ))

/-- The row-letter counts of `fixedIntegerHiveWeightOfShapeEquivLRTableau hlam hμ hν h` agree with
`hiveRowCount h.val`. -/
@[simp] theorem rowCount_fixedIntegerHiveWeightOfShapeEquivLRTableau
    (h : FixedIntegerHive
      (productBoundary (weightOfShape n lam) (weightOfShape n μ) (weightOfShape n ν)))
    (r k : ℕ) :
    (fixedIntegerHiveWeightOfShapeEquivLRTableau hlam hμ hν h).val.rowCount r k =
      hiveRowCount h.val r k := by
  simp [fixedIntegerHiveWeightOfShapeEquivLRTableau]

/-- Evaluating the inverse of `fixedIntegerHiveWeightOfShapeEquivLRTableau` at `p : Vertex n` gives
`lrHiveFun (weightOfShape n lam) T.val p`. -/
@[simp] theorem coe_fixedIntegerHiveWeightOfShapeEquivLRTableau_symm_apply
    (T : LRTableau lam ν μ) (p : Vertex n) :
    ((fixedIntegerHiveWeightOfShapeEquivLRTableau hlam hμ hν).symm T).val p =
      lrHiveFun (weightOfShape n lam) T.val p := by
  simp [fixedIntegerHiveWeightOfShapeEquivLRTableau]

end InverseMap

/-! ### Affine determinant shifts and arbitrary signed dominant weights -/

section DeterminantShift

variable {lam μ γ : DominantWeight n}

section
variable (a b : ℤ) (hlam : (lam.shift a).IsPolynomial) (hμ : (μ.shift b).IsPolynomial)
  (hγ : (γ.shift (a + b)).IsPolynomial)
include hlam hμ hγ

/-- **Shifted hive-to-LR equivalence**: for arbitrary signed dominant weights `λ, μ, γ` and any
shift pair `(a, b)` making `λ.shift a`, `μ.shift b`, and `γ.shift (a + b)` polynomial, adding
`affine n a (a + b)` identifies `FixedIntegerHive (productBoundary λ μ γ)` with
`LRTableau (λ.shift a).shape (γ.shift (a + b)).shape (μ.shift b).shape`. -/
def fixedIntegerHiveShiftEquivLRTableau :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      LRTableau (lam.shift a).shape (γ.shift (a + b)).shape (μ.shift b).shape :=
  (fixedIntegerHiveShiftEquiv lam μ γ a b).trans (fixedIntegerHiveEquivLRTableau hlam hμ hγ)

/-- The row-letter counts of `fixedIntegerHiveShiftEquivLRTableau a b hlam hμ hγ h` agree with
`hiveRowCount h.val` off the diagonal and shift diagonal counts (`r < n`) by `b`, independently of
`a`. -/
@[simp] theorem rowCount_fixedIntegerHiveShiftEquivLRTableau
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r k : ℕ) :
    (fixedIntegerHiveShiftEquivLRTableau a b hlam hμ hγ h).val.rowCount r k =
      if r < n ∧ k = r then (hiveRowCountInt h.val r r + b).toNat
      else hiveRowCount h.val r k := by simp [fixedIntegerHiveShiftEquivLRTableau]

/-- Evaluating the inverse of `fixedIntegerHiveShiftEquivLRTableau a b` at `p : Vertex n` gives
`lrHiveFun lam T.val p - (p.z : ℤ) * b`, independently of `a`. -/
@[simp] theorem coe_fixedIntegerHiveShiftEquivLRTableau_symm_apply
    (T : LRTableau (lam.shift a).shape (γ.shift (a + b)).shape (μ.shift b).shape)
    (p : Vertex n) :
    ((fixedIntegerHiveShiftEquivLRTableau a b hlam hμ hγ).symm T).val p =
      lrHiveFun lam T.val p - (p.z : ℤ) * b := by
  simp only [fixedIntegerHiveShiftEquivLRTableau, Equiv.symm_trans_apply,
    coe_fixedIntegerHiveShiftEquiv_symm_apply, fixedIntegerHiveEquivLRTableau_symm_apply,
    coe_fixedIntegerHiveOfLRTableau, add_apply, hiveOfLRTableau_apply, affine_apply,
    lrHiveFun_shift, Int.nsmul_eq_mul]
  ring

/-- Extracted integer row counts of the inverse of `fixedIntegerHiveShiftEquivLRTableau a b` equal
`T.val.rowCount r k` off the diagonal and `(T.val.rowCount r r : ℤ) - b` on the diagonal
(`r < n`). -/
@[simp] theorem hiveRowCountInt_fixedIntegerHiveShiftEquivLRTableau_symm
    (T : LRTableau (lam.shift a).shape (γ.shift (a + b)).shape (μ.shift b).shape) (r k : ℕ) :
    hiveRowCountInt ((fixedIntegerHiveShiftEquivLRTableau a b hlam hμ hγ).symm T).val r k =
      if r < n ∧ k = r then (T.val.rowCount r r : ℤ) - b else (T.val.rowCount r k : ℤ) := by
  simp only [fixedIntegerHiveShiftEquivLRTableau, Equiv.symm_trans_apply,
    coe_fixedIntegerHiveShiftEquiv_symm_apply, fixedIntegerHiveEquivLRTableau_symm_apply,
    coe_fixedIntegerHiveOfLRTableau, hiveRowCountInt_add,
    hiveRowCountInt_hiveOfLRTableau hlam (DominantWeight.colLen_zero_shape_le _) T,
    hiveRowCountInt_affine]
  split_ifs with h
  · rcases h with ⟨_, rfl⟩; ring
  · simp

end

/-- At shift `(0, 0)` on polynomial weights, `fixedIntegerHiveShiftEquivLRTableau` agrees with
`fixedIntegerHiveEquivLRTableau` up to shape transport along `DominantWeight.shift_zero`. -/
theorem fixedIntegerHiveShiftEquivLRTableau_zero
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial) :
    (fixedIntegerHiveShiftEquivLRTableau 0 0
        (by rwa [DominantWeight.shift_zero]) (by rwa [DominantWeight.shift_zero])
        (by rwa [add_zero, DominantWeight.shift_zero])).trans
      (LRTableau.congr
        (congrArg DominantWeight.shape (DominantWeight.shift_zero lam))
        (congrArg DominantWeight.shape (by rw [add_zero, DominantWeight.shift_zero]))
        (congrArg DominantWeight.shape (DominantWeight.shift_zero μ))) =
      fixedIntegerHiveEquivLRTableau hlam hμ hγ :=
  Equiv.ext fun _ => Subtype.ext (SkewSemistandardYoungTableau.eq_of_rowCount_eq fun _ _ => by
    simp only [Equiv.trans_apply, LRTableau.rowCount_congr,
      rowCount_fixedIntegerHiveShiftEquivLRTableau, add_zero, fixedIntegerHiveEquivLRTableau_apply,
      rowCount_lrTableauOfHive, hiveRowCount]
    split_ifs with hc
    · rw [hc.right]
    · rfl)

section
variable (a₁ b₁ : ℤ) (hlam₁ : (lam.shift a₁).IsPolynomial) (hμ₁ : (μ.shift b₁).IsPolynomial)
  (hγ₁ : (γ.shift (a₁ + b₁)).IsPolynomial)
  (a₂ b₂ : ℤ) (hlam₂ : (lam.shift a₂).IsPolynomial) (hμ₂ : (μ.shift b₂).IsPolynomial)
  (hγ₂ : (γ.shift (a₂ + b₂)).IsPolynomial)
include hlam₁ hμ₁ hγ₁ hlam₂ hμ₂ hγ₂

/-- **Shift independence on the tableau carrier**: for any two shift pairs `(a₁, b₁)` and
`(a₂, b₂)` making all three shifted weights polynomial, composing
`fixedIntegerHiveShiftEquivLRTableau` identifies the corresponding Littlewood–Richardson
tableau types. -/
def lrTableauShiftEquiv :
    LRTableau (lam.shift a₁).shape (γ.shift (a₁ + b₁)).shape (μ.shift b₁).shape ≃
      LRTableau (lam.shift a₂).shape (γ.shift (a₂ + b₂)).shape (μ.shift b₂).shape :=
  (fixedIntegerHiveShiftEquivLRTableau a₁ b₁ hlam₁ hμ₁ hγ₁).symm.trans
    (fixedIntegerHiveShiftEquivLRTableau a₂ b₂ hlam₂ hμ₂ hγ₂)

@[simp] theorem lrTableauShiftEquiv_symm :
    (lrTableauShiftEquiv a₁ b₁ hlam₁ hμ₁ hγ₁ a₂ b₂ hlam₂ hμ₂ hγ₂).symm =
      lrTableauShiftEquiv a₂ b₂ hlam₂ hμ₂ hγ₂ a₁ b₁ hlam₁ hμ₁ hγ₁ := by
  ext T; simp [lrTableauShiftEquiv]

@[simp] theorem lrTableauShiftEquiv_trans (a₃ b₃ : ℤ)
    (hlam₃ : (lam.shift a₃).IsPolynomial) (hμ₃ : (μ.shift b₃).IsPolynomial)
    (hγ₃ : (γ.shift (a₃ + b₃)).IsPolynomial) :
    (lrTableauShiftEquiv a₁ b₁ hlam₁ hμ₁ hγ₁ a₂ b₂ hlam₂ hμ₂ hγ₂).trans
        (lrTableauShiftEquiv a₂ b₂ hlam₂ hμ₂ hγ₂ a₃ b₃ hlam₃ hμ₃ hγ₃) =
      lrTableauShiftEquiv a₁ b₁ hlam₁ hμ₁ hγ₁ a₃ b₃ hlam₃ hμ₃ hγ₃ := by
  ext T; simp [lrTableauShiftEquiv]

/-- Compatibility of `lrTableauShiftEquiv` with `fixedIntegerHiveShiftEquivLRTableau`. -/
@[simp] theorem fixedIntegerHiveShiftEquivLRTableau_trans_lrTableauShiftEquiv :
    (fixedIntegerHiveShiftEquivLRTableau a₁ b₁ hlam₁ hμ₁ hγ₁).trans
        (lrTableauShiftEquiv a₁ b₁ hlam₁ hμ₁ hγ₁ a₂ b₂ hlam₂ hμ₂ hγ₂) =
      fixedIntegerHiveShiftEquivLRTableau a₂ b₂ hlam₂ hμ₂ hγ₂ := by
  ext h; simp [lrTableauShiftEquiv]

/-- `lrTableauShiftEquiv` preserves the hive recovered by `fixedIntegerHiveShiftEquivLRTableau`. -/
@[simp] theorem fixedIntegerHiveShiftEquivLRTableau_symm_lrTableauShiftEquiv
    (T : LRTableau (lam.shift a₁).shape (γ.shift (a₁ + b₁)).shape (μ.shift b₁).shape) :
    (fixedIntegerHiveShiftEquivLRTableau a₂ b₂ hlam₂ hμ₂ hγ₂).symm
        (lrTableauShiftEquiv a₁ b₁ hlam₁ hμ₁ hγ₁ a₂ b₂ hlam₂ hμ₂ hγ₂ T) =
      (fixedIntegerHiveShiftEquivLRTableau a₁ b₁ hlam₁ hμ₁ hγ₁).symm T := by
  simp [lrTableauShiftEquiv]

/-- Exact integer row-count shift formula for `lrTableauShiftEquiv`: off-diagonal counts are
preserved and diagonal counts (`r < n`) shift by `b₂ - b₁`, independently of `a₁` and `a₂`. -/
theorem natCast_rowCount_lrTableauShiftEquiv
    (T : LRTableau (lam.shift a₁).shape (γ.shift (a₁ + b₁)).shape (μ.shift b₁).shape) (r k : ℕ) :
    ((lrTableauShiftEquiv a₁ b₁ hlam₁ hμ₁ hγ₁ a₂ b₂ hlam₂ hμ₂ hγ₂ T).val.rowCount r k : ℤ) =
      if r < n ∧ k = r then (T.val.rowCount r r : ℤ) + (b₂ - b₁) else (T.val.rowCount r k : ℤ) := by
  have h := congrArg (fun x => hiveRowCountInt x.val r k)
    (fixedIntegerHiveShiftEquivLRTableau_symm_lrTableauShiftEquiv
      a₁ b₁ hlam₁ hμ₁ hγ₁ a₂ b₂ hlam₂ hμ₂ hγ₂ T)
  simp only [hiveRowCountInt_fixedIntegerHiveShiftEquivLRTableau_symm] at h
  split_ifs at h ⊢ with hcond
  · rcases hcond with ⟨_, rfl⟩; linarith
  · exact h

/-- Row-letter counts of `lrTableauShiftEquiv` agree with `T.val.rowCount` off the diagonal and
shift diagonal counts (`r < n`) by `b₂ - b₁`, independently of `a₁` and `a₂`. -/
@[simp] theorem rowCount_lrTableauShiftEquiv
    (T : LRTableau (lam.shift a₁).shape (γ.shift (a₁ + b₁)).shape (μ.shift b₁).shape) (r k : ℕ) :
    (lrTableauShiftEquiv a₁ b₁ hlam₁ hμ₁ hγ₁ a₂ b₂ hlam₂ hμ₂ hγ₂ T).val.rowCount r k =
      if r < n ∧ k = r then ((T.val.rowCount r r : ℤ) + (b₂ - b₁)).toNat
      else T.val.rowCount r k := by
  simpa [apply_ite Int.toNat] using congrArg Int.toNat
    (natCast_rowCount_lrTableauShiftEquiv a₁ b₁ hlam₁ hμ₁ hγ₁ a₂ b₂ hlam₂ hμ₂ hγ₂ T r k)

end

@[simp] theorem lrTableauShiftEquiv_self (a b : ℤ) (hlam : (lam.shift a).IsPolynomial)
    (hμ : (μ.shift b).IsPolynomial) (hγ : (γ.shift (a + b)).IsPolynomial) :
    lrTableauShiftEquiv a b hlam hμ hγ a b hlam hμ hγ = Equiv.refl _ :=
  Equiv.symm_trans_self _

variable (hdet : lam.detShift + μ.detShift ≤ γ.detShift)
include hdet

/-- **Canonical signed hive-to-LR equivalence**: for arbitrary signed dominant weights `λ, μ, γ`
satisfying `λ.detShift + μ.detShift ≤ γ.detShift`, subtracting `λ.detShift` and `μ.detShift`
identifies `FixedIntegerHive (productBoundary λ μ γ)` with the Littlewood–Richardson tableaux of
shape `(γ.shift (-(λ.detShift + μ.detShift))).shape / λ.detShiftShape` and content
`μ.detShiftShape`. -/
def fixedIntegerHiveSignedEquivLRTableau :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      LRTableau lam.detShiftShape (γ.shift (-(lam.detShift + μ.detShift))).shape
        μ.detShiftShape :=
  (fixedIntegerHiveShiftEquivLRTableau (-lam.detShift) (-μ.detShift)
    (DominantWeight.isPolynomial_shift_neg_detShift lam)
    (DominantWeight.isPolynomial_shift_neg_detShift μ)
    (DominantWeight.isPolynomial_shift_of_neg_detShift_le (by omega))).trans
    (LRTableau.congr (DominantWeight.shape_shift_neg_detShift lam)
      (congrArg (fun c => (γ.shift c).shape) (neg_add lam.detShift μ.detShift).symm)
      (DominantWeight.shape_shift_neg_detShift μ))

/-- `fixedIntegerHiveSignedEquivLRTableau` is `fixedIntegerHiveShiftEquivLRTableau` at the
canonical shift `(-λ.detShift, -μ.detShift)`, transported to `detShiftShape` by
`LRTableau.congr`. -/
theorem fixedIntegerHiveSignedEquivLRTableau_def :
    fixedIntegerHiveSignedEquivLRTableau hdet =
      (fixedIntegerHiveShiftEquivLRTableau (-lam.detShift) (-μ.detShift)
        (DominantWeight.isPolynomial_shift_neg_detShift lam)
        (DominantWeight.isPolynomial_shift_neg_detShift μ)
        (DominantWeight.isPolynomial_shift_of_neg_detShift_le (by omega))).trans
        (LRTableau.congr (DominantWeight.shape_shift_neg_detShift lam)
          (congrArg (fun c => (γ.shift c).shape) (neg_add lam.detShift μ.detShift).symm)
          (DominantWeight.shape_shift_neg_detShift μ)) := (rfl)

/-- The row-letter counts of `fixedIntegerHiveSignedEquivLRTableau hdet h` agree with
`hiveRowCount h.val` off the diagonal and shift diagonal counts (`r < n`) by `-μ.detShift`. -/
@[simp] theorem rowCount_fixedIntegerHiveSignedEquivLRTableau
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r k : ℕ) :
    (fixedIntegerHiveSignedEquivLRTableau hdet h).val.rowCount r k =
      if r < n ∧ k = r then (hiveRowCountInt h.val r r - μ.detShift).toNat
      else hiveRowCount h.val r k := by simp [fixedIntegerHiveSignedEquivLRTableau, sub_eq_add_neg]

/-- Evaluating the inverse of `fixedIntegerHiveSignedEquivLRTableau` at `p : Vertex n` gives
`lrHiveFun lam T.val p + (p.z : ℤ) * μ.detShift`. -/
@[simp] theorem coe_fixedIntegerHiveSignedEquivLRTableau_symm_apply
    (T : LRTableau lam.detShiftShape (γ.shift (-(lam.detShift + μ.detShift))).shape
      μ.detShiftShape) (p : Vertex n) :
    ((fixedIntegerHiveSignedEquivLRTableau hdet).symm T).val p =
      lrHiveFun lam T.val p + (p.z : ℤ) * μ.detShift := by
  simp [fixedIntegerHiveSignedEquivLRTableau]

/-- Extracted integer row counts of the inverse of `fixedIntegerHiveSignedEquivLRTableau` equal
`T.val.rowCount r k` off the diagonal and `(T.val.rowCount r r : ℤ) + μ.detShift` on the diagonal
(`r < n`). -/
@[simp] theorem hiveRowCountInt_fixedIntegerHiveSignedEquivLRTableau_symm
    (T : LRTableau lam.detShiftShape (γ.shift (-(lam.detShift + μ.detShift))).shape
      μ.detShiftShape) (r k : ℕ) :
    hiveRowCountInt ((fixedIntegerHiveSignedEquivLRTableau hdet).symm T).val r k =
      if r < n ∧ k = r then (T.val.rowCount r r : ℤ) + μ.detShift
      else (T.val.rowCount r k : ℤ) := by simp [fixedIntegerHiveSignedEquivLRTableau]

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
    T.val.rowCount 1 0 = 1 ∧
      detTwo (Vertex.ofChart 2 1 1 le_rfl (by decide)) = 1 ∧
      detTwo (Vertex.ofChart 2 1 2 (by decide) le_rfl) = 2 := by
  refine ⟨?_, by simp, by simp⟩
  rw [fixedIntegerHiveEquivLRTableau_apply, rowCount_lrTableauOfHive, hiveRowCount,
    hiveRowCountInt_of_lt _ (by decide) (by decide)]
  simp

end Checks

end TauCeti.Hive
