/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
import TauCeti.Data.Finset.Basic
public import TauCeti.Analysis.Normed.Module.Alternating.ConjCoeff
public import TauCeti.Analysis.Normed.Module.Alternating.Complex
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import TauCeti.Data.Finset.Sort

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

/-- Alternation of the conjugate-linear derivative of an alternating-map field is the signed
sum of the conjugate Wirtinger derivatives of its evaluations on the omitted tuples. -/
theorem alternatizeUncurryFin_complexAntilinearPartL_fderiv_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {k : ℕ}
    {Θ : E → E [⋀^Fin k]→L[ℝ] F} {z : E} (hd : DifferentiableAt ℝ Θ z)
    (v : Fin (k + 1) → E) :
    ContinuousAlternatingMap.alternatizeUncurryFin
        (ContinuousLinearMap.complexAntilinearPartL (fderiv ℝ Θ z)) v =
      ∑ i : Fin (k + 1), (-1 : ℂ) ^ (i : ℕ) •
        conjWirtingerDeriv (fun y ↦ Θ y (i.removeNth v)) z (v i) := by
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [conjWirtingerDeriv_apply_eq_complexAntilinearPartL]
  simp only [ContinuousLinearMap.complexAntilinearPartL_apply_apply,
    fderiv_continuousAlternatingMap_apply_const_apply hd,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply]
  norm_cast

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

/-- The coordinate differential of coefficients agreeing near a point with evaluations of a
differentiable alternating-map field is the alternation of its conjugate-linear derivative. -/
theorem delBarCoeff_eq_alternatizeUncurryFin {k : ℕ}
    {Θ : (ι → ℂ) → (ι → ℂ) [⋀^Fin k]→L[ℝ] F} {z : ι → ℂ}
    (hd : DifferentiableAt ℝ Θ z) {a : Finset ι → (ι → ℂ) → F}
    {I : Finset ι} (hI : #I = k + 1)
    (ha : ∀ J, #J = k → a J =ᶠ[𝓝 z] fun y ↦ (Θ y).conjCoeff J) :
    delBarCoeff a I z = ContinuousAlternatingMap.alternatizeUncurryFin
      (ContinuousLinearMap.complexAntilinearPartL (fderiv ℝ Θ z))
        (fun i ↦ Pi.single (I.orderEmbOfFin hI i) 1) := by
  let e := I.orderEmbOfFin hI
  rw [alternatizeUncurryFin_complexAntilinearPartL_fderiv_apply hd, delBarCoeff_def]
  conv_lhs => rw [← Finset.sum_coe_sort I, ← (I.orderIsoOfFin hI).toEquiv.sum_comp]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  have hcard : #(I.erase (e b)) = k := by
    rw [card_erase_of_mem (I.orderEmbOfFin_mem hI b), hI, Nat.add_sub_cancel]
  have herase := removeNth_orderEmbOfFin_symm_eq (e b) I (I.orderEmbOfFin_mem hI b) hI hcard
  have heb : (⟨e b, I.orderEmbOfFin_mem hI b⟩ : I) = I.orderIsoOfFin hI b :=
    Subtype.ext (coe_orderIsoOfFin_apply ..).symm
  rw [heb, OrderIso.symm_apply_apply] at herase
  have hcoeff : a (I.erase (e b)) =ᶠ[𝓝 z]
      fun y ↦ Θ y (b.removeNth fun c ↦ (Pi.single (e c) 1 : ι → ℂ)) := by
    filter_upwards [ha _ hcard] with y hy
    rw [hy, ContinuousAlternatingMap.conjCoeff_of_card_eq _ hcard, ← herase]
    exact congrArg _ (funext fun c ↦
      (Fin.removeNth_apply b (fun c ↦ (Pi.single (e c) 1 : ι → ℂ)) c).symm)
  rw [RelIso.coe_fn_toEquiv, coe_orderIsoOfFin_apply, card_filter_lt_orderEmbOfFin,
    hcoeff.conjWirtingerDeriv_eq]

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

/-- `bar∂` commutes with constant complex scaling. -/
theorem delBarCoeff_const_smul (c : ℂ) {u : Finset ι → (ι → ℂ) → F} {I : Finset ι}
    {z : ι → ℂ} : delBarCoeff (c • u) I z = c • delBarCoeff u I z := by
  simp only [delBarCoeff_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Pi.smul_apply, conjWirtingerDeriv_const_smul, _root_.smul_apply, smul_comm]

/-- `bar∂` commutes with negation. -/
theorem delBarCoeff_neg {u : Finset ι → (ι → ℂ) → F} {I : Finset ι} {z : ι → ℂ} :
    delBarCoeff (-u) I z = -delBarCoeff u I z := by
  rw [← neg_one_smul ℂ u, delBarCoeff_const_smul, neg_one_smul]

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

/-- **`bar∂ bar∂ = 0`.** For a coordinate `(0,q)`-form whose coefficients indexed by `I` with two
distinct elements removed are `C²` at `z`, the coefficient of `d(conj z)_I` in `bar∂ bar∂ u`
vanishes at `z`. -/
theorem delBarCoeff_delBarCoeff {u : Finset ι → (ι → ℂ) → F} {I : Finset ι} {z : ι → ℂ}
    (hu : ∀ j ∈ I, ∀ i ∈ I.erase j, ContDiffAt ℝ 2 (u ((I.erase j).erase i)) z) :
    delBarCoeff (delBarCoeff u) I z = 0 := by
  -- The second derivatives `∂²u_{I \ {i,j}}/∂(conj z_j)∂(conj z_i)`, with their signs.
  set D : ι → ι → F := fun j i ↦ ((-1 : ℂ) ^ #{x ∈ I | x < j} *
    (-1) ^ #{x ∈ I.erase j | x < i}) • conjWirtingerDeriv
      (fun y ↦ conjWirtingerDeriv (u ((I.erase j).erase i)) y (Pi.single i 1)) z (Pi.single j 1)
    with hD
  have hexp : delBarCoeff (delBarCoeff u) I z = ∑ j ∈ I, ∑ i ∈ I.erase j, D j i := by
    rw [delBarCoeff_def]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [conjWirtingerDeriv_delBarCoeff_apply (hu j hj), Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by simp only [hD, mul_smul]
  -- Exchanging `i` and `j` changes the sign of `D j i`.
  have hanti {i j : ι} (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) : D i j = -D j i := by
    have hc : conjWirtingerDeriv (fun y ↦ conjWirtingerDeriv (u ((I.erase i).erase j)) y
          (Pi.single j 1)) z (Pi.single i 1) =
        conjWirtingerDeriv (fun y ↦ conjWirtingerDeriv (u ((I.erase j).erase i)) y
          (Pi.single i 1)) z (Pi.single j 1) := by
      rw [Finset.erase_right_comm,
        conjWirtingerDeriv_conjWirtingerDeriv_comm (hu j hj i (Finset.mem_erase.2 ⟨hij, hi⟩))]
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
