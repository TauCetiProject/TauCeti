/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Data.Finset.Basic

/-!
# The operator `bar∂` on `(0,q)`-forms in coordinates

On the coordinate space `ι → ℂ` of a linearly ordered index type `ι`, a `(0,q)`-form with
coefficients in a complex normed space `F` is a sum `∑_J u_J d(conj z)_J` over the subsets `J` of
`ι` with `q` elements, where `d(conj z)_J = d(conj z_{j₁}) ∧ ⋯ ∧ d(conj z_{j_q})` for the
increasing enumeration `j₁ < ⋯ < j_q` of `J`. Such a form is recorded by its family of coefficients
`u : Finset ι → (ι → ℂ) → F`; only the coefficients indexed by sets with `q` elements matter.

Its `bar∂` is the `(0,q+1)`-form `∑_j ∂u_J/∂(conj z_j) d(conj z_j) ∧ d(conj z)_J`. Moving
`d(conj z_j)` to its place in the increasing enumeration of `I = insert j J` costs the sign
`(-1)^#{i ∈ I | i < j}`, so the coefficient of `d(conj z)_I` is
`TauCeti.delBarCoeff u I z = ∑_{j ∈ I} (-1)^#{i ∈ I | i < j} ∂u_{I \ {j}}/∂(conj z_j)`.

The operator is additive on differentiable coefficients, preserves smoothness and squares to zero
on `C²` coefficients, since the second conjugate Wirtinger derivatives commute. These are the
coordinate `(0,q)`-forms of the Dolbeault–Grothendieck lemma on polydiscs in
`TauCeti.Analysis.Complex.Wirtinger.Polydisc`. A `(p,q)`-form `∑_{I,J} u_{I,J} dz_I ∧ d(conj z)_J`
is the `(0,q)`-form with coefficients `J ↦ (I ↦ u_{I,J})` in `Finset ι → F`, and its `bar∂` is
`(-1)^p` times the `bar∂` of that `(0,q)`-form.

## Main declarations

* `TauCeti.delBarCoeff`: the coefficients of `bar∂` of a coordinate `(0,q)`-form.
* `TauCeti.delBarCoeff_add`, `TauCeti.delBarCoeff_sub`: additivity on differentiable
  coefficients.
* `TauCeti.contDiffAt_delBarCoeff`: `bar∂` of a form with `C^(m+1)` coefficients has `C^m`
  coefficients.
* `TauCeti.delBarCoeff_delBarCoeff`: `bar∂ bar∂ = 0` on forms with `C²` coefficients.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Section 2.1.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0, §2.
-/

public section

open Complex Filter Finset Topology

namespace TauCeti

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- The coefficients of `bar∂ u` for a coordinate `(0,q)`-form `u = ∑_J u_J d(conj z)_J` on
`ι → ℂ`: the coefficient of `d(conj z)_I` is
`∑_{j ∈ I} (-1)^#{i ∈ I | i < j} ∂u_{I \ {j}}/∂(conj z_j)`. Here `d(conj z)_I` is the wedge
product of the `d(conj z_i)`, `i ∈ I`, in increasing order. -/
noncomputable def delBarCoeff (u : Finset ι → (ι → ℂ) → F) (I : Finset ι) (z : ι → ℂ) : F :=
  ∑ j ∈ I, (-1 : ℂ) ^ #{i ∈ I | i < j} • conjWirtingerDeriv (u (I.erase j)) z (Pi.single j 1)

/-- The defining formula of `TauCeti.delBarCoeff`. -/
theorem delBarCoeff_def (u : Finset ι → (ι → ℂ) → F) (I : Finset ι) (z : ι → ℂ) :
    delBarCoeff u I z =
      ∑ j ∈ I, (-1 : ℂ) ^ #{i ∈ I | i < j} •
        conjWirtingerDeriv (u (I.erase j)) z (Pi.single j 1) :=
  (rfl)

/-- The function-valued defining formula used to differentiate `delBarCoeff`. -/
private theorem delBarCoeff_eq_fun (u : Finset ι → (ι → ℂ) → F) (I : Finset ι) :
    delBarCoeff u I = fun z ↦ ∑ j ∈ I, (-1 : ℂ) ^ #{i ∈ I | i < j} •
      conjWirtingerDeriv (u (I.erase j)) z (Pi.single j 1) :=
  funext (delBarCoeff_def u I)

/-- The coefficient of `bar∂ u` indexed by the empty set vanishes. -/
@[simp]
theorem delBarCoeff_empty (u : Finset ι → (ι → ℂ) → F) : delBarCoeff u ∅ = 0 := by
  ext z
  simp [delBarCoeff_def]

/-- A singleton coefficient of `bar∂ u` is a conjugate coordinate derivative of `u ∅`. -/
@[simp]
theorem delBarCoeff_singleton (u : Finset ι → (ι → ℂ) → F) (j : ι) (z : ι → ℂ) :
    delBarCoeff u {j} z = conjWirtingerDeriv (u ∅) z (Pi.single j 1) := by
  simp [delBarCoeff_def, Finset.filter_singleton]

/-- A two-element coefficient of `bar∂ u` is the difference of two coordinate derivatives. -/
theorem delBarCoeff_pair (u : Finset ι → (ι → ℂ) → F) {a b : ι} (hab : a < b) (z : ι → ℂ) :
    delBarCoeff u {a, b} z = conjWirtingerDeriv (u {b}) z (Pi.single a 1) -
      conjWirtingerDeriv (u {a}) z (Pi.single b 1) := by
  rw [delBarCoeff_def, Finset.sum_pair hab.ne, Finset.erase_insert (by simpa using hab.ne),
    Finset.erase_insert_of_ne hab.ne, Finset.erase_singleton]
  simp [Finset.filter_insert, Finset.filter_singleton, hab, hab.not_gt, sub_eq_add_neg]

/-- `bar∂` of the zero form vanishes. -/
@[simp]
theorem delBarCoeff_zero : delBarCoeff (0 : Finset ι → (ι → ℂ) → F) = 0 := by
  ext I z
  simp [delBarCoeff_def]

/-- The coefficient of `bar∂ u` at `z` only depends on the germs at `z` of the coefficients. -/
theorem delBarCoeff_congr {u w : Finset ι → (ι → ℂ) → F} {I : Finset ι} {z : ι → ℂ}
    (h : ∀ j ∈ I, u (I.erase j) =ᶠ[𝓝 z] w (I.erase j)) :
    delBarCoeff u I z = delBarCoeff w I z :=
  Finset.sum_congr rfl fun j hj ↦ by rw [(h j hj).conjWirtingerDeriv_eq]

/-- `bar∂` is additive on forms whose coefficients are real-differentiable. -/
theorem delBarCoeff_add {u w : Finset ι → (ι → ℂ) → F} {I : Finset ι} {z : ι → ℂ}
    (hu : ∀ j ∈ I, DifferentiableAt ℝ (u (I.erase j)) z)
    (hw : ∀ j ∈ I, DifferentiableAt ℝ (w (I.erase j)) z) :
    delBarCoeff (u + w) I z = delBarCoeff u I z + delBarCoeff w I z := by
  simp only [delBarCoeff_def, ← Finset.sum_add_distrib, ← smul_add]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Pi.add_apply, conjWirtingerDeriv_add (hu j hj) (hw j hj), _root_.add_apply]

/-- `bar∂` commutes with subtraction of forms whose coefficients are real-differentiable. -/
theorem delBarCoeff_sub {u w : Finset ι → (ι → ℂ) → F} {I : Finset ι} {z : ι → ℂ}
    (hu : ∀ j ∈ I, DifferentiableAt ℝ (u (I.erase j)) z)
    (hw : ∀ j ∈ I, DifferentiableAt ℝ (w (I.erase j)) z) :
    delBarCoeff (u - w) I z = delBarCoeff u I z - delBarCoeff w I z := by
  simp only [delBarCoeff_def, ← Finset.sum_sub_distrib, ← smul_sub]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Pi.sub_apply, conjWirtingerDeriv_sub (hu j hj) (hw j hj), _root_.sub_apply]

/-- `bar∂` commutes with constant complex scaling of real-differentiable coefficients. -/
theorem delBarCoeff_const_smul (c : ℂ) {u : Finset ι → (ι → ℂ) → F} {I : Finset ι}
    {z : ι → ℂ} (hu : ∀ j ∈ I, DifferentiableAt ℝ (u (I.erase j)) z) :
    delBarCoeff (c • u) I z = c • delBarCoeff u I z := by
  simp only [delBarCoeff_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Pi.smul_apply, conjWirtingerDeriv_const_smul (hu j hj), _root_.smul_apply, smul_comm]

/-- `bar∂` commutes with negation of real-differentiable coefficients. -/
theorem delBarCoeff_neg {u : Finset ι → (ι → ℂ) → F} {I : Finset ι} {z : ι → ℂ}
    (hu : ∀ j ∈ I, DifferentiableAt ℝ (u (I.erase j)) z) :
    delBarCoeff (-u) I z = -delBarCoeff u I z := by
  simpa only [neg_one_smul] using delBarCoeff_const_smul (-1) hu

/-- `bar∂` of a form whose coefficients are `C^(m+1)` at `z` has `C^m` coefficients at `z`. -/
theorem contDiffAt_delBarCoeff {u : Finset ι → (ι → ℂ) → F} {I : Finset ι} {z : ι → ℂ}
    {m n : WithTop ℕ∞} (hu : ∀ j ∈ I, ContDiffAt ℝ n (u (I.erase j)) z) (hmn : m + 1 ≤ n) :
    ContDiffAt ℝ m (delBarCoeff u I) z := by
  rw [delBarCoeff_eq_fun]
  exact ContDiffAt.sum fun j hj ↦ ((hu j hj).conjWirtingerDeriv_apply hmn _).const_smul _

/-- For a form with `C²` coefficients, the conjugate Wirtinger derivative of a coefficient of
`bar∂ u` is the alternating sum of the second conjugate Wirtinger derivatives of the
coefficients of `u`. -/
private theorem conjWirtingerDeriv_delBarCoeff_apply {u : Finset ι → (ι → ℂ) → F}
    {J : Finset ι} {z : ι → ℂ} (hu : ∀ i ∈ J, ContDiffAt ℝ 2 (u (J.erase i)) z) (v : ι → ℂ) :
    conjWirtingerDeriv (delBarCoeff u J) z v =
      ∑ i ∈ J, (-1 : ℂ) ^ #{x ∈ J | x < i} •
        conjWirtingerDeriv (fun y ↦ conjWirtingerDeriv (u (J.erase i)) y (Pi.single i 1)) z v := by
  have hd (i : ι) (hi : i ∈ J) : DifferentiableAt ℝ
      (fun y ↦ conjWirtingerDeriv (u (J.erase i)) y (Pi.single i 1)) z :=
    ((hu i hi).hasFDerivAt_conjWirtingerDeriv_apply _).differentiableAt
  have hD : fderiv ℝ (delBarCoeff u J) z = ∑ i ∈ J, (-1 : ℂ) ^ #{x ∈ J | x < i} •
      fderiv ℝ (fun y ↦ conjWirtingerDeriv (u (J.erase i)) y (Pi.single i 1)) z := by
    rw [delBarCoeff_eq_fun, fderiv_fun_sum (A := fun i y ↦ (-1 : ℂ) ^ #{x ∈ J | x < i} •
        conjWirtingerDeriv (u (J.erase i)) y (Pi.single i 1)) fun i hi ↦ (hd i hi).const_smul _]
    exact Finset.sum_congr rfl fun i hi ↦ fderiv_fun_const_smul (hd i hi) _
  rw [conjWirtingerDeriv_eq_sum_smul hD, _root_.sum_apply]
  simp only [_root_.smul_apply]

/-- **`bar∂ bar∂ = 0`.** For a coordinate `(0,q)`-form whose coefficients indexed by subsets of `I`
are `C²` at `z`, the coefficient of `d(conj z)_I` in `bar∂ bar∂ u` vanishes at `z`. -/
theorem delBarCoeff_delBarCoeff {u : Finset ι → (ι → ℂ) → F} {I : Finset ι} {z : ι → ℂ}
    (hu : ∀ J ⊆ I, ContDiffAt ℝ 2 (u J) z) :
    delBarCoeff (delBarCoeff u) I z = 0 := by
  -- The second derivatives `∂²u_{I \ {i,j}}/∂(conj z_j)∂(conj z_i)`, with their signs.
  set D : ι → ι → F := fun j i ↦ ((-1 : ℂ) ^ #{x ∈ I | x < j} *
    (-1) ^ #{x ∈ I.erase j | x < i}) • conjWirtingerDeriv
      (fun y ↦ conjWirtingerDeriv (u ((I.erase j).erase i)) y (Pi.single i 1)) z (Pi.single j 1)
    with hD
  have hexp : delBarCoeff (delBarCoeff u) I z = ∑ j ∈ I, ∑ i ∈ I.erase j, D j i := by
    rw [delBarCoeff_def]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [conjWirtingerDeriv_delBarCoeff_apply fun i hi ↦ hu _
      (((I.erase j).erase_subset i).trans (I.erase_subset j)), Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by simp only [hD, mul_smul]
  -- Exchanging `i` and `j` changes the sign of `D j i`.
  have hanti {i j : ι} (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) : D i j = -D j i := by
    have hc : conjWirtingerDeriv (fun y ↦ conjWirtingerDeriv (u ((I.erase i).erase j)) y
          (Pi.single j 1)) z (Pi.single i 1) =
        conjWirtingerDeriv (fun y ↦ conjWirtingerDeriv (u ((I.erase j).erase i)) y
          (Pi.single i 1)) z (Pi.single j 1) := by
      rw [Finset.erase_right_comm, conjWirtingerDeriv_conjWirtingerDeriv_comm (hu _
        (((I.erase j).erase_subset i).trans (I.erase_subset j)))]
    have hs : (-1 : ℂ) ^ #{x ∈ I | x < i} * (-1) ^ #{x ∈ I.erase i | x < j} =
        -((-1 : ℂ) ^ #{x ∈ I | x < j} * (-1) ^ #{x ∈ I.erase j | x < i}) :=
      Finset.neg_one_pow_card_filter_lt_mul_erase hi hj hij
    simp only [hD]
    rw [hc, hs, neg_smul]
  have hswap : ∑ j ∈ I, ∑ i ∈ I.erase j, D j i = -∑ j ∈ I, ∑ i ∈ I.erase j, D j i := calc
    _ = ∑ i ∈ I, ∑ j ∈ I.erase i, D j i :=
      Finset.sum_comm' fun j i ↦ by simp only [Finset.mem_erase]; grind
    _ = ∑ i ∈ I, ∑ j ∈ I.erase i, -D i j :=
      Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦
        hanti (Finset.mem_erase.1 hj).2 hi (Finset.mem_erase.1 hj).1
    _ = _ := by simp only [Finset.sum_neg_distrib]
  have h2 : (2 : ℂ) • ∑ j ∈ I, ∑ i ∈ I.erase j, D j i = 0 := by
    rw [two_smul]
    nth_rewrite 1 [hswap]
    exact neg_add_cancel _
  rw [hexp]
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

end TauCeti
