/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import TauCeti.Combinatorics.Optimization.QuadraticBinary.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.SimpleGraph.Bipartite
import TauCeti.Order.Filter.Extr

/-!
# Ancilla field elimination and reductions between QUBO, Ising, and Max-Cut

This module extends `TauCeti.Combinatorics.Optimization.QuadraticBinary.Basic` with two exact
combinatorial reductions:

* **Ancilla field elimination** (`TauCeti.ising_ancilla`): introducing one auxiliary spin `none` on
  `Option ι` yields an explicit coupling matrix `TauCeti.isingAncillaMatrix J h` whose field-free
  Ising energy equals `ising J h fun i ↦ xor (y (some i)) (y none)`. The projection
  `y ↦ (fun i ↦ xor (y (some i)) (y none))` is two-to-one and surjective, so the infimum and
  minimizers are preserved (`TauCeti.iInf_ising_ancilla`, `TauCeti.isMinOn_ising_ancilla_iff`).
* **Cut weights and QUBO-to-Max-Cut** (`TauCeti.cutWeight`): defines the cut weight
  `∑ i, ∑ j, w i j * bit x i * (1 - bit x j)` of a real weight matrix `w`, shows that for a simple
  graph `G`, `cutWeight (G.adjMatrix ℝ) x` counts the edges between `{i | x i = true}` and its
  complement (`SimpleGraph.cutWeight_adjMatrix_eq_card_between`), relates symmetric cuts to
  field-free Ising energies (`TauCeti.cutWeight_eq_ising`), relates arbitrary cuts to QUBOs
  (`TauCeti.cutWeight_eq_neg_qubo`), and reduces every QUBO on `ι` to the negative of a symmetric
  cut weight on `Option ι` with no additive constant (`TauCeti.qubo_eq_neg_cutWeight`).

## Main definitions

* `TauCeti.isingAncillaMatrix`: the coupling matrix on `Option ι` absorbing linear fields `h`.
* `TauCeti.cutWeight`: the cut weight objective for a matrix `w`.
* `TauCeti.quboCutMatrix`: the symmetric weight matrix on `Option ι` reducing `qubo Q` to a cut.

## Main results

* `TauCeti.ising_ancilla`, `TauCeti.xor_option_surjective`, `TauCeti.card_filter_xor_option_eq`,
  `TauCeti.isMinOn_ising_ancilla_iff`: ancilla elimination of external fields.
* `SimpleGraph.cutWeight_adjMatrix_eq_card_between`, `TauCeti.cutWeight_eq_ising`,
  `TauCeti.cutWeight_eq_neg_qubo`: graph cut counting and cut–Ising–QUBO identities.
* `TauCeti.qubo_eq_neg_cutWeight`, `TauCeti.iInf_qubo_eq_neg_iSup_cutWeight`,
  `TauCeti.isMinOn_qubo_iff_isMaxOn_cutWeight`: reduction from QUBO minimization to Max-Cut.

## References

* D. P. Williamson and D. B. Shmoys, *The design of approximation algorithms*, Cambridge
  University Press, 2011, Lemma 6.3.
-/

noncomputable section

public section

open Finset Matrix

namespace TauCeti

/-! ### Ancilla elimination of linear fields -/

section Ancilla

variable {ι : Type*}

/-- The coupling matrix on `Option ι` that absorbs the external field `h` of `ising J h` into
couplings with the ancilla spin `none`. -/
def isingAncillaMatrix (J : Matrix ι ι ℝ) (h : ι → ℝ) : Matrix (Option ι) (Option ι) ℝ :=
  Matrix.of fun a b ↦ match a, b with
    | some i, some j => J i j
    | some i, none => h i / 2
    | none, some j => h j / 2
    | none, none => 0

theorem isingAncillaMatrix_apply (J : Matrix ι ι ℝ) (h : ι → ℝ) (a b : Option ι) :
    isingAncillaMatrix J h a b = match a, b with
      | some i, some j => J i j
      | some i, none => h i / 2
      | none, some j => h j / 2
      | none, none => 0 :=
  (rfl)

@[simp]
theorem isingAncillaMatrix_some_some (J : Matrix ι ι ℝ) (h : ι → ℝ) (i j : ι) :
    isingAncillaMatrix J h (some i) (some j) = J i j :=
  (rfl)

@[simp]
theorem isingAncillaMatrix_some_none (J : Matrix ι ι ℝ) (h : ι → ℝ) (i : ι) :
    isingAncillaMatrix J h (some i) none = h i / 2 :=
  (rfl)

@[simp]
theorem isingAncillaMatrix_none_some (J : Matrix ι ι ℝ) (h : ι → ℝ) (j : ι) :
    isingAncillaMatrix J h none (some j) = h j / 2 :=
  (rfl)

@[simp]
theorem isingAncillaMatrix_none_none (J : Matrix ι ι ℝ) (h : ι → ℝ) :
    isingAncillaMatrix J h none none = 0 :=
  (rfl)

theorem isSymm_isingAncillaMatrix {J : Matrix ι ι ℝ} (hJ : J.IsSymm) (h : ι → ℝ) :
    (isingAncillaMatrix J h).IsSymm := by
  ext a b
  cases a <;> cases b <;> simp [hJ.apply]

/-- Eliminating external fields by coupling to one ancilla spin `none`: the field-free Ising
energy on `Option ι` equals the original Ising energy evaluated at `i ↦ xor (y (some i)) (y none)`.
-/
theorem ising_ancilla [Fintype ι] (J : Matrix ι ι ℝ) (h : ι → ℝ) (y : Option ι → Bool) :
    ising (isingAncillaMatrix J h) 0 y = ising J h fun i ↦ xor (y (some i)) (y none) := by
  let x : ι → Bool := fun i ↦ xor (y (some i)) (y none)
  have hspin (i : ι) : spin y (some i) = spin x i * spin y none := by
    cases h1 : y (some i) <;> cases h2 : y none <;> simp [x, h1, h2]
  simp only [ising_def, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
    Fintype.sum_option, isingAncillaMatrix_none_none, isingAncillaMatrix_none_some,
    isingAncillaMatrix_some_none, isingAncillaMatrix_some_some, zero_add,
    Finset.sum_add_distrib]
  have hquad :
      (∑ i : ι, ∑ j : ι, J i j * spin y (some i) * spin y (some j)) =
        ∑ i : ι, ∑ j : ι, J i j * spin x i * spin x j := by
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hspin i, hspin j]
    calc
      J i j * (spin x i * spin y none) * (spin x j * spin y none)
        = J i j * spin x i * spin x j * (spin y none * spin y none) := by ring
      _ = J i j * spin x i * spin x j := by rw [spin_mul_spin, mul_one]
  have hlin :
      (∑ i : ι, (h i / 2) * spin y (some i) * spin y none) +
          (∑ j : ι, (h j / 2) * spin y none * spin y (some j)) =
        ∑ i : ι, h i * spin x i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hspin i]
    calc
      (h i / 2) * (spin x i * spin y none) * spin y none +
          (h i / 2) * spin y none * (spin x i * spin y none)
        = h i * spin x i * (spin y none * spin y none) := by ring
      _ = h i * spin x i := by rw [spin_mul_spin, mul_one]
  rw [hquad, ← hlin]
  ring

/-- The ancilla-relative projection `y ↦ (i ↦ xor (y (some i)) (y none))` from `Option ι → Bool`
to `ι → Bool` is surjective. -/
theorem xor_option_surjective (ι : Type*) :
    Function.Surjective fun (y : Option ι → Bool) (i : ι) ↦ xor (y (some i)) (y none) :=
  fun x ↦ ⟨fun a ↦ Option.elim a false x, by ext i; simp⟩

/-- A configuration `y : Option ι → Bool` projects to `x : ι → Bool` under `xor` with the ancilla
spin `y none` if and only if `y` extends `x` with `none ↦ false` or its global flip `!x` with
`none ↦ true`. -/
theorem xor_option_eq_iff (y : Option ι → Bool) (x : ι → Bool) :
    (fun i ↦ xor (y (some i)) (y none)) = x ↔
      y = (fun a ↦ Option.elim a false x) ∨ y = (fun a ↦ Option.elim a true fun i ↦ !x i) := by
  constructor
  · intro h
    cases hnone : y none
    · left
      ext a
      cases a with
      | none => simp [hnone]
      | some i => simpa [hnone] using congrFun h i
    · right
      ext a
      cases a with
      | none => simp [hnone]
      | some i =>
        have hi := congrFun h i
        simp only [hnone, Bool.xor_true] at hi
        simp [← hi]
  · rintro (rfl | rfl) <;> ext i <;> simp

/-- Every fiber of the ancilla-relative projection `y ↦ (i ↦ xor (y (some i)) (y none))` has
cardinality `2`. -/
theorem card_filter_xor_option_eq [Fintype ι] [DecidableEq ι] (x : ι → Bool) :
    #{y : Option ι → Bool | (fun i ↦ xor (y (some i)) (y none)) = x} = 2 := by
  have hset :
      (Finset.univ.filter fun y : Option ι → Bool ↦ (fun i ↦ xor (y (some i)) (y none)) = x) =
        {fun a ↦ Option.elim a false x, fun a ↦ Option.elim a true fun i ↦ !x i} := by
    ext y
    simp [xor_option_eq_iff]
  have hne : (fun a : Option ι ↦ Option.elim a false x) ≠
      (fun a : Option ι ↦ Option.elim a true fun i ↦ !x i) := by
    intro h
    have h0 := congrFun h none
    simp at h0
  rw [hset, Finset.card_pair hne]

/-- Ancilla elimination preserves the global infimum of an Ising model. -/
theorem iInf_ising_ancilla [Fintype ι] (J : Matrix ι ι ℝ) (h : ι → ℝ) :
    ⨅ y : Option ι → Bool, ising (isingAncillaMatrix J h) 0 y = ⨅ x : ι → Bool, ising J h x :=
  (xor_option_surjective ι).iInf_congr _ fun y ↦ (ising_ancilla J h y).symm

/-- Ancilla elimination preserves global minimizers along the xor projection: `y` minimizes
`ising (isingAncillaMatrix J h) 0` if and only if `i ↦ xor (y (some i)) (y none)` minimizes
`ising J h`. -/
theorem isMinOn_ising_ancilla_iff [Fintype ι] (J : Matrix ι ι ℝ) (h : ι → ℝ) (y : Option ι → Bool) :
    IsMinOn (ising (isingAncillaMatrix J h) 0) Set.univ y ↔
      IsMinOn (ising J h) Set.univ fun i ↦ xor (y (some i)) (y none) := by
  rw [funext (ising_ancilla J h)]
  exact (xor_option_surjective ι).isMinOn_univ_comp_iff (ising J h) y

end Ancilla

/-! ### Cut weights and the reduction from QUBO to Max-Cut -/

section Cuts

variable {ι : Type*} [Fintype ι]

/-- The cut weight of a configuration `x : ι → Bool` with respect to a real weight matrix `w`:
the total weight of ordered pairs `(i, j)` with `x i = true` and `x j = false`. -/
def cutWeight (w : Matrix ι ι ℝ) (x : ι → Bool) : ℝ :=
  ∑ i, ∑ j, w i j * bit x i * (1 - bit x j)

theorem cutWeight_def (w : Matrix ι ι ℝ) (x : ι → Bool) :
    cutWeight w x = ∑ i, ∑ j, w i j * bit x i * (1 - bit x j) :=
  (rfl)

@[simp]
theorem cutWeight_zero (x : ι → Bool) : cutWeight (0 : Matrix ι ι ℝ) x = 0 := by
  simp [cutWeight_def]

@[simp]
theorem cutWeight_add (w₁ w₂ : Matrix ι ι ℝ) (x : ι → Bool) :
    cutWeight (w₁ + w₂) x = cutWeight w₁ x + cutWeight w₂ x := by
  simp [cutWeight_def, add_mul, sum_add_distrib]

@[simp]
theorem cutWeight_sub (w₁ w₂ : Matrix ι ι ℝ) (x : ι → Bool) :
    cutWeight (w₁ - w₂) x = cutWeight w₁ x - cutWeight w₂ x := by
  simp [cutWeight_def, sub_mul, sum_sub_distrib]

@[simp]
theorem cutWeight_neg (w : Matrix ι ι ℝ) (x : ι → Bool) :
    cutWeight (-w) x = -cutWeight w x := by
  simp [cutWeight_def, sum_neg_distrib]

@[simp]
theorem cutWeight_smul (c : ℝ) (w : Matrix ι ι ℝ) (x : ι → Bool) :
    cutWeight (c • w) x = c * cutWeight w x := by
  simp [cutWeight_def, mul_assoc, mul_sum]

@[simp]
theorem cutWeight_diagonal [DecidableEq ι] (d : ι → ℝ) (x : ι → Bool) :
    cutWeight (Matrix.diagonal d) x = 0 := by
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [Fintype.sum_eq_single i]
  · cases h : x i <;> simp [h]
  · intro j hji
    simp [hji.symm]

theorem cutWeight_sub_diagonal [DecidableEq ι] (w : Matrix ι ι ℝ) (x : ι → Bool) :
    cutWeight (w - Matrix.diagonal w.diag) x = cutWeight w x := by
  rw [cutWeight_sub, cutWeight_diagonal, sub_zero]

theorem cutWeight_not (w : Matrix ι ι ℝ) (x : ι → Bool) :
    cutWeight w (fun i ↦ !x i) = cutWeight wᵀ x := by
  simp only [cutWeight_def, bit_not, transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

theorem cutWeight_not_of_isSymm {w : Matrix ι ι ℝ} (hw : w.IsSymm) (x : ι → Bool) :
    cutWeight w (fun i ↦ !x i) = cutWeight w x := by
  rw [cutWeight_not, hw.eq]

end Cuts

end TauCeti

namespace SimpleGraph

section

variable {ι : Type*} [Fintype ι]

private theorem cutWeight_adjMatrix_eq_sum_card_filter (G : SimpleGraph ι) [DecidableRel G.Adj]
    [DecidableEq ι] (x : ι → Bool) :
    TauCeti.cutWeight (G.adjMatrix ℝ) x =
      ∑ v ∈ Finset.univ.filter (fun i ↦ x i = true),
        ((#{w ∈ (Finset.univ.filter fun i ↦ x i = true)ᶜ | G.Adj v w} : ℕ) : ℝ) := by
  set s : Finset ι := Finset.univ.filter fun i ↦ x i = true
  simp only [TauCeti.cutWeight_def, adjMatrix_apply, Finset.card_filter]
  have houter (v : ι) :
      (∑ j : ι, (if G.Adj v j then (1 : ℝ) else 0) * TauCeti.bit x v * (1 - TauCeti.bit x j)) =
        if v ∈ s then ∑ w ∈ sᶜ, if G.Adj v w then (1 : ℝ) else 0 else 0 := by
    by_cases hv : x v = true
    · have hvs : v ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
      simp only [hvs, ↓reduceIte]
      rw [← Finset.sum_add_sum_compl s]
      have hs0 :
          ∑ j ∈ s, (if G.Adj v j then (1 : ℝ) else 0) * TauCeti.bit x v * (1 - TauCeti.bit x j) =
            0 :=
        Finset.sum_eq_zero fun j hj ↦ by
          have hjtrue : x j = true := (Finset.mem_filter.mp hj).2
          simp [hjtrue]
      rw [hs0, zero_add]
      refine Finset.sum_congr rfl fun w hw ↦ ?_
      have hwfalse : x w = false := Bool.eq_false_iff.mpr fun hwt ↦
        (Finset.mem_compl.mp hw) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwt⟩)
      simp [hv, hwfalse]
    · have hvs : v ∉ s := fun h ↦ hv (Finset.mem_filter.mp h).2
      have hvf : x v = false := Bool.eq_false_iff.mpr hv
      simp [hvs, hvf]
  simp_rw [houter, ← Finset.sum_filter]
  have hfilt : Finset.univ.filter (· ∈ s) = s := by ext v; simp
  rw [hfilt]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  simp only [Nat.cast_sum, Nat.cast_one]

/-- For a simple graph `G`, `TauCeti.cutWeight (G.adjMatrix ℝ) x` counts the edges of `G` with one
endpoint where `x` is `true` and one endpoint where `x` is `false`. -/
theorem cutWeight_adjMatrix_eq_card_between (G : SimpleGraph ι) [DecidableRel G.Adj]
    (x : ι → Bool) :
    TauCeti.cutWeight (G.adjMatrix ℝ) x =
      ((G.between {i | x i = true} {i | x i = true}ᶜ).edgeFinset.card : ℝ) := by
  classical
  let s : Finset ι := Finset.univ.filter fun i ↦ x i = true
  have hs : (s : Set ι) = {i | x i = true} := by ext i; simp [s]
  have hcard :
      #(G.between (s : Set ι) (s : Set ι)ᶜ).edgeFinset = ∑ v ∈ s, #{w ∈ sᶜ | G.Adj v w} :=
    G.card_edgeFinset_between_compl s
  have hB :
      (G.between (s : Set ι) (s : Set ι)ᶜ).edgeFinset =
        (G.between {i | x i = true} {i | x i = true}ᶜ).edgeFinset := by
    ext e
    simp [hs]
  rw [cutWeight_adjMatrix_eq_sum_card_filter, ← Nat.cast_sum, ← hcard, hB]

end

end SimpleGraph

namespace TauCeti

section Cuts

variable {ι : Type*} [Fintype ι]

/-- For symmetric weights `w`, the cut weight is an explicit affine shift of the field-free Ising
energy with coupling matrix `(1 / 4) • w`. -/
theorem cutWeight_eq_ising {w : Matrix ι ι ℝ} (hw : w.IsSymm) (x : ι → Bool) :
    cutWeight w x = (∑ i, ∑ j, w i j) / 4 - ising ((1 / 4 : ℝ) • w) 0 x := by
  simp only [cutWeight_def, ising_def, Matrix.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, bit_eq_one_sub_spin_div_two]
  have h1 :
      (∑ i, ∑ j, w i j * ((1 - spin x i) / 2) * (1 - (1 - spin x j) / 2)) =
        (∑ i, ∑ j, w i j) / 4 - (∑ i, ∑ j, w i j * spin x i / 4) +
          (∑ i, ∑ j, w i j * spin x j / 4) -
          ∑ i, ∑ j, (1 / 4 * w i j) * spin x i * spin x j := by
    simp only [Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hcancel : (∑ i, ∑ j, w i j * spin x i / 4) = ∑ i, ∑ j, w i j * spin x j / 4 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hw.apply]
  rw [h1, hcancel]
  ring

/-- For symmetric weights `w`, global maximizers of `cutWeight w` are the same as global
minimizers of the field-free Ising energy `ising ((1 / 4 : ℝ) • w) 0`. -/
theorem isMaxOn_cutWeight_iff_isMinOn_ising {w : Matrix ι ι ℝ} (hw : w.IsSymm) (x : ι → Bool) :
    IsMaxOn (cutWeight w) Set.univ x ↔ IsMinOn (ising ((1 / 4 : ℝ) • w) 0) Set.univ x := by
  simp only [isMaxOn_univ_iff, isMinOn_univ_iff, cutWeight_eq_ising hw, sub_le_sub_iff_left]

/-- Every cut weight (for arbitrary, possibly asymmetric `w`) is the negative of an explicit
QUBO objective. -/
theorem cutWeight_eq_neg_qubo [DecidableEq ι] (w : Matrix ι ι ℝ) (x : ι → Bool) :
    cutWeight w x = -qubo (w - Matrix.diagonal fun i ↦ ∑ j, w i j) x := by
  rw [qubo_sub, qubo_diagonal]
  simp only [cutWeight_def, qubo_def, mul_sub, mul_one, Finset.sum_sub_distrib]
  have hlin : (∑ i, ∑ j, w i j * bit x i) = ∑ i, (∑ j, w i j) * bit x i :=
    Finset.sum_congr rfl fun i _ ↦ (Finset.sum_mul _ _ _).symm
  rw [hlin]
  ring

/-- The symmetric weight matrix on `Option ι` satisfying
`cutWeight (quboCutMatrix Q) y = -qubo Q fun i ↦ xor (y (some i)) (y none)`, where the ancilla
`none` sets the reference side. -/
def quboCutMatrix (Q : Matrix ι ι ℝ) : Matrix (Option ι) (Option ι) ℝ :=
  Matrix.of fun a b ↦ match a, b with
    | some i, some j => (Q i j + Q j i) / 2
    | some i, none => -(∑ k, (Q i k + Q k i)) / 2
    | none, some j => -(∑ k, (Q j k + Q k j)) / 2
    | none, none => 0

theorem quboCutMatrix_apply (Q : Matrix ι ι ℝ) (a b : Option ι) :
    quboCutMatrix Q a b = match a, b with
      | some i, some j => (Q i j + Q j i) / 2
      | some i, none => -(∑ k, (Q i k + Q k i)) / 2
      | none, some j => -(∑ k, (Q j k + Q k j)) / 2
      | none, none => 0 :=
  (rfl)

@[simp]
theorem quboCutMatrix_some_some (Q : Matrix ι ι ℝ) (i j : ι) :
    quboCutMatrix Q (some i) (some j) = (Q i j + Q j i) / 2 :=
  (rfl)

@[simp]
theorem quboCutMatrix_some_none (Q : Matrix ι ι ℝ) (i : ι) :
    quboCutMatrix Q (some i) none = -(∑ k, (Q i k + Q k i)) / 2 :=
  (rfl)

@[simp]
theorem quboCutMatrix_none_some (Q : Matrix ι ι ℝ) (j : ι) :
    quboCutMatrix Q none (some j) = -(∑ k, (Q j k + Q k j)) / 2 :=
  (rfl)

@[simp]
theorem quboCutMatrix_none_none (Q : Matrix ι ι ℝ) :
    quboCutMatrix Q none none = 0 :=
  (rfl)

@[simp]
theorem isSymm_quboCutMatrix (Q : Matrix ι ι ℝ) : (quboCutMatrix Q).IsSymm := by
  ext a b
  cases a <;> cases b <;> simp [add_comm]

/-- Every quadratic pseudo-Boolean function `qubo Q` on `ι`, evaluated at the xor projection
`y ↦ (i ↦ xor (y (some i)) (y none))` where the ancilla `none` sets the reference side, equals
`-cutWeight (quboCutMatrix Q) y` with no additive constant. -/
theorem qubo_eq_neg_cutWeight (Q : Matrix ι ι ℝ) (y : Option ι → Bool) :
    qubo Q (fun i ↦ xor (y (some i)) (y none)) = -cutWeight (quboCutMatrix Q) y := by
  let h : ι → ℝ := fun i ↦ -(∑ j, (Q i j + Q j i)) / 4
  have htotal : (∑ a : Option ι, ∑ b : Option ι, quboCutMatrix Q a b) = -(∑ i, ∑ j, Q i j) := by
    simp only [Fintype.sum_option, quboCutMatrix_none_none, quboCutMatrix_none_some,
      quboCutMatrix_some_none, quboCutMatrix_some_some, zero_add, Finset.sum_add_distrib]
    have hss : (∑ i, ∑ j, (Q i j + Q j i) / 2) = ∑ i, ∑ j, Q i j := by
      have hswap : (∑ i, ∑ j, Q j i) = ∑ i, ∑ j, Q i j := Finset.sum_comm
      calc
        ∑ i, ∑ j, (Q i j + Q j i) / 2
          = ((∑ i, ∑ j, Q i j) + ∑ i, ∑ j, Q j i) / 2 := by
              simp only [← Finset.sum_div, Finset.sum_add_distrib]
        _ = ∑ i, ∑ j, Q i j := by rw [hswap]; ring
    have hsn : (∑ i, -(∑ k, Q i k + ∑ k, Q k i) / 2) = -(∑ i, ∑ j, Q i j) := by
      have hswap : (∑ i, ∑ k, Q k i) = ∑ i, ∑ k, Q i k := Finset.sum_comm
      simp only [neg_div, Finset.sum_neg_distrib, ← Finset.sum_div, Finset.sum_add_distrib,
        hswap]
      ring
    rw [hss, hsn]
    ring
  have hising_eq :
      ising ((1 / 4 : ℝ) • quboCutMatrix Q) 0 y =
        ising (isingAncillaMatrix ((1 / 4 : ℝ) • Q) h) 0 y := by
    have hsymm :
        (1 / 4 : ℝ) • quboCutMatrix Q =
          (1 / 2 : ℝ) • (isingAncillaMatrix ((1 / 4 : ℝ) • Q) h +
            (isingAncillaMatrix ((1 / 4 : ℝ) • Q) h)ᵀ) := by
      ext a b
      cases a <;> cases b <;>
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul,
          quboCutMatrix_none_none, quboCutMatrix_none_some, quboCutMatrix_some_none,
          quboCutMatrix_some_some, isingAncillaMatrix_none_none, isingAncillaMatrix_none_some,
          isingAncillaMatrix_some_none, isingAncillaMatrix_some_some, h] <;> ring
    rw [hsymm, ising_symmetrize]
  rw [cutWeight_eq_ising (isSymm_quboCutMatrix Q) y, htotal, hising_eq, ising_ancilla,
    qubo_eq_ising]
  ring

/-- The global infimum of `qubo Q` equals minus the max-cut supremum of `quboCutMatrix Q`. -/
theorem iInf_qubo_eq_neg_iSup_cutWeight (Q : Matrix ι ι ℝ) :
    ⨅ x : ι → Bool, qubo Q x = -⨆ y : Option ι → Bool, cutWeight (quboCutMatrix Q) y := by
  have hb : BddAbove (Set.range fun y : Option ι → Bool ↦ cutWeight (quboCutMatrix Q) y) :=
    Set.Finite.bddAbove (Set.finite_range _)
  have hneg :
      -⨆ y : Option ι → Bool, cutWeight (quboCutMatrix Q) y =
        ⨅ y : Option ι → Bool, -cutWeight (quboCutMatrix Q) y :=
    (OrderIso.neg ℝ).map_ciSup hb
  rw [hneg]
  exact ((xor_option_surjective ι).iInf_congr _ fun y ↦ qubo_eq_neg_cutWeight Q y).symm

/-- Global maximizers `y` of `cutWeight (quboCutMatrix Q)` correspond to global minimizers of
`qubo Q` through the xor projection `i ↦ xor (y (some i)) (y none)`. -/
theorem isMinOn_qubo_iff_isMaxOn_cutWeight (Q : Matrix ι ι ℝ) (y : Option ι → Bool) :
    IsMinOn (qubo Q) Set.univ (fun i ↦ xor (y (some i)) (y none)) ↔
      IsMaxOn (cutWeight (quboCutMatrix Q)) Set.univ y := by
  rw [← (xor_option_surjective ι).isMinOn_univ_comp_iff (qubo Q) y]
  simp only [isMinOn_univ_iff, isMaxOn_univ_iff, Function.comp_apply,
    qubo_eq_neg_cutWeight, neg_le_neg_iff]

end Cuts

end TauCeti
