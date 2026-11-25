/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.UniversalCentralExtension
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.GroupTheory.Commutator

/-!
# Weyl and diagonal elements of the Steinberg group

For distinct indices `i ≠ j` and a unit `u` of a ring `R`, the Steinberg group `St_ι(R)` contains
the **Weyl element** `w_{ij}(u) = x_{ij}(u) x_{ji}(-u⁻¹) x_{ij}(u)` and the **diagonal element**
`h_{ij}(u) = w_{ij}(u) w_{ij}(-1)`. In `GL ι R` they map to the monomial matrix with entries `u` at
`(i, j)` and `-u⁻¹` at `(j, i)`, and to the diagonal matrix `diag(u at i, u⁻¹ at j)`.

These elements carry the computations behind Steinberg symbols. For a commutative ring `R` and
units `u`, `v`, the Steinberg symbol `{u, v}` is the commutator `⁅h_{ij}(u), h_{ik}(v)⁆` of lifts
of the commuting matrices `diag(u, u⁻¹, 1)` and `diag(v, 1, v⁻¹)`. Matsumoto's theorem presents
`K₂` of a field by these symbols subject to bimultiplicativity and the Steinberg relation
`{u, 1 - u} = 1`. This file proves those relations in the stable Steinberg group `St(R)`.

Conjugation by `w_{ij}(u)` permutes the root subgroups by the transposition of `i` and `j`,
twisted by `u` (Milnor, §9). This gives `w_{ji}(-u⁻¹) = w_{ij}(u)` and the
commutator formula `⁅h_{ij}(u), h_{ik}(v)⁆ = h_{ij}(u) h_{ij}(v) h_{ij}(v u)⁻¹`. Writing
`x_{ij}(1) = x_{ij}(u) x_{ij}(v)` when `u + v = 1` and expanding each factor through
`w_{ij}` gives the identity `w_{ij}(u) w_{ij}(v) = w_{ij}(u v⁻¹) w_{ij}(1)`. With
`h_{ij}(-u) h_{ij}(u⁻¹) = h_{ij}(-1)`, this yields the exact relations `{u, v⁻¹} = 1` and
`{-u, u⁻¹} = 1` in every `St_ι(R)` with three distinct indices. In `St(R)` the symbols lie in
`K₂(R)`, which is central, so they are bimultiplicative, and the Steinberg relation and
`{u, -u} = 1` follow.

## Main definitions

* `TauCeti.IndexedSteinbergGroup.w`: the Weyl element `w_{ij}(u)`.
* `TauCeti.IndexedSteinbergGroup.h`: the diagonal element `h_{ij}(u)`.

## Main results

* `TauCeti.IndexedSteinbergGroup.w_mul_x_mul_inv_ik` and its five companions: conjugation of the
  generators by `w_{ij}(u)`; `TauCeti.IndexedSteinbergGroup.h_mul_x_mul_inv_ik` and its companions
  for `h_{ij}(u)`.
* `TauCeti.IndexedSteinbergGroup.w_symm_neg_inv`: `w_{ji}(-u⁻¹) = w_{ij}(u)`.
* `TauCeti.IndexedSteinbergGroup.commutatorElement_h_h`: the commutator of `h_{ij}(u)` and
  `h_{ik}(v)`.
* `TauCeti.IndexedSteinbergGroup.w_mul_w_of_add_eq_one`: the identity
  `w_{ij}(u) w_{ij}(v) = w_{ij}(u v⁻¹) w_{ij}(1)` for `u + v = 1`.
* `TauCeti.IndexedSteinbergGroup.commutatorElement_h_h_inv_of_add_eq_one`,
  `TauCeti.IndexedSteinbergGroup.commutatorElement_h_neg_h_inv`: the exact relations
  `{u, v⁻¹} = 1` for `u + v = 1` and `{-u, u⁻¹} = 1`.
* `TauCeti.IndexedSteinbergGroup.toGL_h`, `TauCeti.SteinbergGroup.toStableGL_h`: the image of
  `h_{ij}(u)` in `GL ι R`, respectively `GL_∞(R)`, is a diagonal matrix.
* `TauCeti.SteinbergGroup.commutatorElement_h_h_mem_ker`: over a commutative ring, symbols lie in
  `K₂(R) = ker (St(R) → GL_∞(R))`.
* `TauCeti.SteinbergGroup.commutatorElement_h_h_mul_left`,
  `TauCeti.SteinbergGroup.commutatorElement_h_h_mul_right`: bimultiplicativity of symbols.
* `TauCeti.SteinbergGroup.commutatorElement_h_h_of_add_eq_one`: the Steinberg relation
  `{u, v} = 1` for `u + v = 1`.
* `TauCeti.SteinbergGroup.commutatorElement_h_h_neg`: `{u, -u} = 1`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §9.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, Definition 5.10, and §6.
-/

public section

open scoped commutatorElement

namespace TauCeti

namespace IndexedSteinbergGroup

variable {ι R : Type*} [Ring R]

/-! ### The elements `w_{ij}(u)` and `h_{ij}(u)` -/

/-- The **Weyl element** `w_{ij}(u) = x_{ij}(u) x_{ji}(-u⁻¹) x_{ij}(u)` of the Steinberg group,
for distinct indices `i ≠ j` and a unit `u`. For finite `ι` its image in `GL ι R` is the monomial
matrix with entries `u` at `(i, j)`, `-u⁻¹` at `(j, i)`, and those of the identity off rows and
columns `i` and `j` (`coe_toGL_w`). -/
def w {i j : ι} (hij : i ≠ j) (u : Rˣ) : IndexedSteinbergGroup ι R :=
  x hij (u : R) * x hij.symm (-(u⁻¹ : Rˣ) : R) * x hij (u : R)

theorem w_def {i j : ι} (hij : i ≠ j) (u : Rˣ) :
    w hij u = x hij (u : R) * x hij.symm (-(u⁻¹ : Rˣ) : R) * x hij (u : R) :=
  (rfl)

/-- The **diagonal element** `h_{ij}(u) = w_{ij}(u) w_{ij}(-1)` of the Steinberg group, for
distinct indices `i ≠ j` and a unit `u`. For finite `ι` its image in `GL ι R` is the diagonal
matrix with `u` at `i`, `u⁻¹` at `j` and `1` elsewhere (`toGL_h`). -/
def h {i j : ι} (hij : i ≠ j) (u : Rˣ) : IndexedSteinbergGroup ι R :=
  w hij u * w hij (-1)

theorem h_def {i j : ι} (hij : i ≠ j) (u : Rˣ) : h hij u = w hij u * w hij (-1) :=
  (rfl)

/-- Inverting a Weyl element negates its unit. -/
@[simp]
theorem w_inv {i j : ι} (hij : i ≠ j) (u : Rˣ) : (w hij u)⁻¹ = w hij (-u) := by
  simp only [w_def, mul_inv_rev, x_inv, inv_neg, Units.val_neg, neg_neg, mul_assoc]

@[simp]
theorem w_mul_w_neg {i j : ι} (hij : i ≠ j) (u : Rˣ) : w hij u * w hij (-u) = 1 := by
  rw [← w_inv, mul_inv_cancel]

@[simp]
theorem w_neg_mul_w {i j : ι} (hij : i ≠ j) (u : Rˣ) : w hij (-u) * w hij u = 1 := by
  rw [← w_inv, inv_mul_cancel]

@[simp]
theorem h_one {i j : ι} (hij : i ≠ j) : h hij (1 : Rˣ) = 1 := by
  rw [h_def, ← w_inv, mul_inv_cancel]

/-- A product of two Weyl elements at the same pair of indices, in terms of diagonal elements:
`w_{ij}(u) w_{ij}(v) = h_{ij}(u) h_{ij}(-v)⁻¹`. -/
theorem w_mul_w {i j : ι} (hij : i ≠ j) (u v : Rˣ) :
    w hij u * w hij v = h hij u * (h hij (-v))⁻¹ := by
  simp only [h_def, mul_inv_rev, w_inv, neg_neg, mul_assoc]
  rw [← mul_assoc (w hij (-1)), w_neg_mul_w, one_mul]

/-! ### Functoriality -/

@[simp]
theorem map_w {S : Type*} [Ring S] (f : R →+* S) {i j : ι} (hij : i ≠ j) (u : Rˣ) :
    map f (w hij u) = w hij (Units.map (f : R →* S) u) := by
  simp [w_def]

@[simp]
theorem map_h {S : Type*} [Ring S] (f : R →+* S) {i j : ι} (hij : i ≠ j) (u : Rˣ) :
    map f (h hij u) = h hij (Units.map (f : R →* S) u) := by
  simp [h_def]

@[simp]
theorem mapIndex_w {κ : Type*} (e : ι ↪ κ) {i j : ι} (hij : i ≠ j) (u : Rˣ) :
    mapIndex (R := R) e (w hij u) = w (e.injective.ne hij) u := by
  simp [w_def]

@[simp]
theorem mapIndex_h {κ : Type*} (e : ι ↪ κ) {i j : ι} (hij : i ≠ j) (u : Rˣ) :
    mapIndex (R := R) e (h hij u) = h (e.injective.ne hij) u := by
  simp [h_def]

/-! ### Conjugation of the generators by Weyl elements -/

private theorem conj_x_commute {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (a b : R) : MulAut.conj (x hij a) (x hkl b) = x hkl b := by
  rw [MulAut.conj_apply, (commute_x hij hkl hjk hli a b).mul_inv_cancel]

private theorem conj_x_chain {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    MulAut.conj (x hij a) (x hjk b) = x hik (a * b) * x hjk b := by
  rw [MulAut.conj_apply, x_mul_x_mul_inv hij hjk hik]

private theorem conj_x_reverse {i j k : ι} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (a b : R) :
    MulAut.conj (x hij a) (x hki b) = x hkj (-(b * a)) * x hki b := by
  rw [MulAut.conj_apply, x_mul_x_mul_inv_reverse hij hki hkj]

/-- Products of two commuting root families: `x_p(a) x_q(b) x_p(c) = x_p(a + c) x_q(b)`. -/
private theorem x_mul_x_mul_x_of_commute {i j k l : ι} {hij : i ≠ j} {hkl : k ≠ l}
    (hc : ∀ a b : R, Commute (x hij a) (x hkl b)) (a b c : R) :
    x hij a * x hkl b * x hij c = x hij (a + c) * x hkl b := by
  rw [mul_assoc, ← (hc c b).eq, ← mul_assoc, ← x_add]

/-- Products of two commuting root families:
`x_p(a) x_q(b) x_p(c) (x_p(d) x_q(e)) = x_p(a + c + d) x_q(b + e)`. -/
private theorem x_mul_x_mul_x_mul_x_mul_x_of_commute {i j k l : ι} {hij : i ≠ j} {hkl : k ≠ l}
    (hc : ∀ a b : R, Commute (x hij a) (x hkl b)) (a b c d e : R) :
    x hij a * x hkl b * x hij c * (x hij d * x hkl e) = x hij (a + c + d) * x hkl (b + e) := by
  rw [x_mul_x_mul_x_of_commute hc, ← mul_assoc, mul_assoc (x hij (a + c)), ← (hc d b).eq,
    ← mul_assoc, ← x_add, mul_assoc, ← x_add]

/-- Conjugating `x_{ik}(v)` by `w_{ij}(u)`, for pairwise distinct `i, j, k`, gives
`x_{jk}(-u⁻¹ v)`. -/
theorem w_mul_x_mul_inv_ik {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (v : R) : w hij u * x hik v * (w hij u)⁻¹ = x hjk (-((u⁻¹ : Rˣ) * v)) := by
  rw [← MulAut.conj_apply, w_def]
  simp only [map_mul, MulAut.mul_apply, conj_x_commute, conj_x_chain, ne_eq, not_false_eq_true,
    hij.symm, hik, hik.symm, hjk]
  rw [x_mul_x_mul_x_of_commute fun a b ↦ commute_x hik hjk hjk.symm hik.symm a b]
  simp

/-- Conjugating `x_{jk}(v)` by `w_{ij}(u)`, for pairwise distinct `i, j, k`, gives
`x_{ik}(u v)`. -/
theorem w_mul_x_mul_inv_jk {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (v : R) : w hij u * x hjk v * (w hij u)⁻¹ = x hik ((u : R) * v) := by
  rw [← MulAut.conj_apply, w_def]
  simp only [map_mul, MulAut.mul_apply, conj_x_commute, conj_x_chain, ne_eq, not_false_eq_true,
    hij, hij.symm, hik, hik.symm, hjk, hjk.symm]
  rw [x_mul_x_mul_x_mul_x_mul_x_of_commute fun a b ↦ commute_x hik hjk hjk.symm hik.symm a b]
  simp

/-- Conjugating `x_{ki}(v)` by `w_{ij}(u)`, for pairwise distinct `i, j, k`, gives
`x_{kj}(-v u)`. -/
theorem w_mul_x_mul_inv_ki {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (v : R) : w hij u * x hik.symm v * (w hij u)⁻¹ = x hjk.symm (-(v * u)) := by
  rw [← MulAut.conj_apply, w_def]
  simp only [map_mul, MulAut.mul_apply, conj_x_commute, conj_x_reverse, ne_eq, not_false_eq_true,
    hij, hij.symm, hik, hik.symm, hjk, hjk.symm]
  rw [x_mul_x_mul_x_mul_x_mul_x_of_commute
    fun a b ↦ commute_x hjk.symm hik.symm hjk hik a b]
  simp [mul_assoc]

/-- Conjugating `x_{kj}(v)` by `w_{ij}(u)`, for pairwise distinct `i, j, k`, gives
`x_{ki}(v u⁻¹)`. -/
theorem w_mul_x_mul_inv_kj {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (v : R) : w hij u * x hjk.symm v * (w hij u)⁻¹ = x hik.symm (v * (u⁻¹ : Rˣ)) := by
  rw [← MulAut.conj_apply, w_def]
  simp only [map_mul, MulAut.mul_apply, conj_x_commute, conj_x_reverse, ne_eq, not_false_eq_true,
    hij.symm, hik, hik.symm, hjk, hjk.symm]
  rw [x_mul_x_mul_x_of_commute fun a b ↦ commute_x hjk.symm hik.symm hjk hik a b]
  simp [mul_assoc]

/-- `w_{ij}(u)` commutes with `x_{kl}(v)` when `k` and `l` both differ from `i` and `j`. -/
theorem commute_w_x {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (u : Rˣ) (v : R) : Commute (w hij u) (x hkl v) := by
  have h₁ := commute_x hij hkl hjk hil.symm (u : R) v
  rw [w_def]
  exact (h₁.mul_left (commute_x hij.symm hkl hik hjl.symm _ v)).mul_left h₁

/-- Conjugating `x_{ij}(v)` by `w_{ij}(u)` gives `x_{ji}(-u⁻¹ v u⁻¹)`, in the presence of a third
index `k`. -/
theorem w_mul_x_mul_inv_ij {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (v : R) :
    w hij u * x hij v * (w hij u)⁻¹ = x hij.symm (-((u⁻¹ : Rˣ) * v * (u⁻¹ : Rˣ))) := by
  rw [← mul_one v, ← commutatorElement_x hik hjk.symm hij, ← MulAut.conj_apply,
    map_commutatorElement, MulAut.conj_apply, MulAut.conj_apply, w_mul_x_mul_inv_ik hij hik hjk,
    w_mul_x_mul_inv_kj hij hik hjk, commutatorElement_x hjk hik.symm hij.symm]
  simp [mul_assoc]

/-- Conjugating `x_{ji}(v)` by `w_{ij}(u)` gives `x_{ij}(-u v u)`, in the presence of a third
index `k`. -/
theorem w_mul_x_mul_inv_ji {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (v : R) : w hij u * x hij.symm v * (w hij u)⁻¹ = x hij (-((u : R) * v * u)) := by
  rw [← mul_one v, ← commutatorElement_x hjk hik.symm hij.symm, ← MulAut.conj_apply,
    map_commutatorElement, MulAut.conj_apply, MulAut.conj_apply, w_mul_x_mul_inv_jk hij hik hjk,
    w_mul_x_mul_inv_ki hij hik hjk, commutatorElement_x hik hjk.symm hij]
  simp [mul_assoc]

/-- The Weyl element of the reversed pair: `w_{ji}(-u⁻¹) = w_{ij}(u)`, in the presence of a third
index `k`. -/
theorem w_symm_neg_inv {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ) :
    w hij.symm (-u⁻¹) = w hij u := by
  have h₁ : w hij u * x hij (u : R) * (w hij u)⁻¹ = x hij.symm (-(u⁻¹ : Rˣ) : R) := by
    rw [w_mul_x_mul_inv_ij hij hik hjk]
    simp
  have h₂ : w hij u * x hij.symm (-(u⁻¹ : Rˣ) : R) * (w hij u)⁻¹ = x hij (u : R) := by
    rw [w_mul_x_mul_inv_ji hij hik hjk]
    simp
  calc w hij.symm (-u⁻¹) = x hij.symm (-(u⁻¹ : Rˣ) : R) * x hij (u : R) *
        x hij.symm (-(u⁻¹ : Rˣ) : R) := by simp [w_def]
    _ = (w hij u * x hij (u : R) * (w hij u)⁻¹) *
        (w hij u * x hij.symm (-(u⁻¹ : Rˣ) : R) * (w hij u)⁻¹) *
          (w hij u * x hij (u : R) * (w hij u)⁻¹) := by rw [h₁, h₂]
    _ = w hij u * (x hij (u : R) * x hij.symm (-(u⁻¹ : Rˣ) : R) * x hij (u : R)) *
        (w hij u)⁻¹ := by group
    _ = w hij u := by rw [← w_def, mul_inv_cancel_right]

/-- Conjugating `w_{ij}(v)` by `w_{ij}(u)` gives `w_{ij}(u v⁻¹ u)`, in the presence of a third
index `k`. -/
theorem w_mul_w_mul_inv {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u v : Rˣ) :
    w hij u * w hij v * (w hij u)⁻¹ = w hij (u * v⁻¹ * u) := by
  rw [← MulAut.conj_apply, w_def hij v, map_mul, map_mul, MulAut.conj_apply,
    w_mul_x_mul_inv_ij hij hik hjk, MulAut.conj_apply, w_mul_x_mul_inv_ji hij hik hjk,
    ← w_symm_neg_inv hij hik hjk, w_def]
  simp [mul_assoc]

/-! ### Conjugation by diagonal elements -/

/-- Conjugation by `h_{ij}(u)` unfolded into conjugations by its two Weyl factors. -/
private theorem h_mul_mul_inv {i j : ι} (hij : i ≠ j) (u : Rˣ) (y : IndexedSteinbergGroup ι R) :
    h hij u * y * (h hij u)⁻¹ = w hij u * (w hij (-1) * y * (w hij (-1))⁻¹) * (w hij u)⁻¹ := by
  rw [h_def]
  group

/-- Conjugating `x_{ik}(v)` by `h_{ij}(u)`, for pairwise distinct `i, j, k`, gives `x_{ik}(u v)`. -/
theorem h_mul_x_mul_inv_ik {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (v : R) : h hij u * x hik v * (h hij u)⁻¹ = x hik ((u : R) * v) := by
  rw [h_mul_mul_inv, w_mul_x_mul_inv_ik hij hik hjk]
  simp only [inv_neg, inv_one, Units.val_neg, Units.val_one, neg_mul, one_mul, neg_neg]
  rw [w_mul_x_mul_inv_jk hij hik hjk]

/-- Conjugating `x_{jk}(v)` by `h_{ij}(u)`, for pairwise distinct `i, j, k`, gives
`x_{jk}(u⁻¹ v)`. -/
theorem h_mul_x_mul_inv_jk {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (v : R) : h hij u * x hjk v * (h hij u)⁻¹ = x hjk ((u⁻¹ : Rˣ) * v) := by
  rw [h_mul_mul_inv, w_mul_x_mul_inv_jk hij hik hjk, w_mul_x_mul_inv_ik hij hik hjk]
  simp

/-- Conjugating `x_{ki}(v)` by `h_{ij}(u)`, for pairwise distinct `i, j, k`, gives
`x_{ki}(v u⁻¹)`. -/
theorem h_mul_x_mul_inv_ki {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (v : R) : h hij u * x hik.symm v * (h hij u)⁻¹ = x hik.symm (v * (u⁻¹ : Rˣ)) := by
  rw [h_mul_mul_inv, w_mul_x_mul_inv_ki hij hik hjk]
  simp only [Units.val_neg, Units.val_one, mul_neg, mul_one, neg_neg]
  rw [w_mul_x_mul_inv_kj hij hik hjk]

/-- Conjugating `x_{kj}(v)` by `h_{ij}(u)`, for pairwise distinct `i, j, k`, gives `x_{kj}(v u)`. -/
theorem h_mul_x_mul_inv_kj {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (v : R) : h hij u * x hjk.symm v * (h hij u)⁻¹ = x hjk.symm (v * u) := by
  rw [h_mul_mul_inv, w_mul_x_mul_inv_kj hij hik hjk, w_mul_x_mul_inv_ki hij hik hjk]
  simp

/-- Conjugating `x_{ij}(v)` by `h_{ij}(u)` gives `x_{ij}(u v u)`, in the presence of a third index
`k`. -/
theorem h_mul_x_mul_inv_ij {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (v : R) : h hij u * x hij v * (h hij u)⁻¹ = x hij ((u : R) * v * u) := by
  rw [h_mul_mul_inv, w_mul_x_mul_inv_ij hij hik hjk, w_mul_x_mul_inv_ji hij hik hjk]
  simp [mul_assoc]

/-- Conjugating `x_{ji}(v)` by `h_{ij}(u)` gives `x_{ji}(u⁻¹ v u⁻¹)`, in the presence of a third
index `k`. -/
theorem h_mul_x_mul_inv_ji {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (v : R) :
    h hij u * x hij.symm v * (h hij u)⁻¹ = x hij.symm ((u⁻¹ : Rˣ) * v * (u⁻¹ : Rˣ)) := by
  rw [h_mul_mul_inv, w_mul_x_mul_inv_ji hij hik hjk, w_mul_x_mul_inv_ij hij hik hjk]
  simp [mul_assoc]

/-- Conjugating `w_{ij}(u)` by `h_{ik}(v)`, for pairwise distinct `i, j, k`, gives
`w_{ij}(v u)`. -/
theorem h_mul_w_mul_inv {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u v : Rˣ) :
    h hik v * w hij u * (h hik v)⁻¹ = w hij (v * u) := by
  rw [← MulAut.conj_apply, w_def, map_mul, map_mul, MulAut.conj_apply,
    h_mul_x_mul_inv_ik hik hij hjk.symm, MulAut.conj_apply, h_mul_x_mul_inv_ki hik hij hjk.symm,
    w_def]
  simp [mul_assoc]

/-! ### Commutators of diagonal elements and the symbol relations -/

/-- The commutator of the diagonal elements `h_{ij}(u)` and `h_{ik}(v)`, for pairwise distinct
`i, j, k`, measures the failure of `h_{ij}` to be multiplicative:
`⁅h_{ij}(u), h_{ik}(v)⁆ = h_{ij}(u) h_{ij}(v) h_{ij}(v u)⁻¹`. -/
theorem commutatorElement_h_h {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u v : Rˣ) :
    ⁅h hij u, h hik v⁆ = h hij u * h hij v * (h hij (v * u))⁻¹ := by
  have hconj : h hik v * h hij u * (h hik v)⁻¹ = h hij (v * u) * (h hij v)⁻¹ := by
    rw [h_def hij u, ← MulAut.conj_apply, map_mul, MulAut.conj_apply, h_mul_w_mul_inv hij hik hjk,
      MulAut.conj_apply, h_mul_w_mul_inv hij hik hjk, w_mul_w]
    simp
  calc ⁅h hij u, h hik v⁆ = h hij u * (h hik v * h hij u * (h hik v)⁻¹)⁻¹ := by
        rw [commutatorElement_def]; group
    _ = h hij u * h hij v * (h hij (v * u))⁻¹ := by rw [hconj]; group

/-- `h_{ij}(-u) h_{ij}(u⁻¹) = h_{ij}(-1)`, in the presence of a third index `k`. -/
theorem h_neg_mul_h_inv {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ) :
    h hij (-u) * h hij u⁻¹ = h hij (-1) := by
  have key := w_mul_w_mul_inv hij hik hjk 1 u
  rw [one_mul, mul_one] at key
  rw [h_def, h_def, h_def, ← key]
  simp only [← w_inv]
  group

/-- **The symbol relation `{-u, u⁻¹} = 1`** in the Steinberg group: the diagonal elements
`h_{ij}(-u)` and `h_{ik}(u⁻¹)` commute, for pairwise distinct `i, j, k`. -/
theorem commutatorElement_h_neg_h_inv {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) : ⁅h hij (-u), h hik u⁻¹⁆ = 1 := by
  rw [commutatorElement_h_h hij hik hjk, h_neg_mul_h_inv hij hik hjk, mul_neg, inv_mul_cancel,
    mul_inv_cancel]

/-! ### Images in the general linear group -/

section FiniteIndex

variable [Fintype ι] [DecidableEq ι]

/-- The image of `w_{ij}(u)` in `GL ι R` is the monomial matrix
`1 - E_{ii} - E_{jj} + u E_{ij} - u⁻¹ E_{ji}`. -/
theorem coe_toGL_w {i j : ι} (hij : i ≠ j) (u : Rˣ) :
    (toGL (w hij u) : Matrix ι ι R) = 1 - Matrix.single i i 1 - Matrix.single j j 1 +
      Matrix.single i j (u : R) - Matrix.single j i ((u⁻¹ : Rˣ) : R) := by
  simp only [w_def, map_mul, Units.val_mul, toGL_x, coe_transvectionUnit_eq_one_add_single]
  simp [mul_add, add_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne,
    hij.symm, ← Matrix.single_neg]
  abel

/-- The image of `h_{ij}(u)` in `GL ι R` is the diagonal matrix with `u` at `i`, `u⁻¹` at `j` and
`1` elsewhere. -/
@[simp]
theorem toGL_h {i j : ι} (hij : i ≠ j) (u : Rˣ) :
    toGL (h hij u) = diagGL (Pi.mulSingle i u * Pi.mulSingle j u⁻¹) := by
  apply Units.ext
  have hprod : (toGL (h hij u) : Matrix ι ι R) = 1 - Matrix.single i i 1 - Matrix.single j j 1 +
      Matrix.single i i (u : R) + Matrix.single j j ((u⁻¹ : Rˣ) : R) := by
    rw [h_def, map_mul, Units.val_mul, coe_toGL_w, coe_toGL_w]
    simp only [sub_eq_add_neg, Matrix.single_neg]
    simp [mul_add, add_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hij,
      hij.symm]
    simp only [← Matrix.single_neg]
    abel
  rw [hprod, diagGL_coe]
  ext p q
  rw [Matrix.diagonal_apply]
  by_cases hpq : p = q
  · subst hpq
    by_cases hpi : p = i
    · subst hpi
      simp [hij.symm]
    · by_cases hpj : p = j
      · subst hpj
        simp [hij]
      · simp [Ne.symm hpi, Ne.symm hpj, hpi, hpj]
  · have hi : ¬(i = p ∧ i = q) := fun h ↦ hpq (h.1.symm.trans h.2)
    have hj : ¬(j = p ∧ j = q) := fun h ↦ hpq (h.1.symm.trans h.2)
    simp [hpq, hi, hj]

end FiniteIndex

end IndexedSteinbergGroup

namespace SteinbergGroup

open IndexedSteinbergGroup

variable {R : Type*} [Ring R]

/-- The canonical map `Stₙ(R) →* St(R)` sends `w_{ij}(u)` to `w_{ij}(u)`. -/
@[simp]
theorem ofFin_w {n : ℕ} {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    ofFin R n (w hij u) = w (Fin.val_ne_of_ne hij) u := by
  simp [w_def]

/-- The canonical map `Stₙ(R) →* St(R)` sends `h_{ij}(u)` to `h_{ij}(u)`. -/
@[simp]
theorem ofFin_h {n : ℕ} {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    ofFin R n (h hij u) = h (Fin.val_ne_of_ne hij) u := by
  simp [h_def]

/-- The image of `h_{ij}(u)` in `GL_∞(R)` is the class of the diagonal matrix in `GL_n(R)` with `u`
at `i`, `u⁻¹` at `j` and `1` elsewhere, for any `n` with `i, j < n`. -/
theorem toStableGL_h {i j : ℕ} (hij : i ≠ j) (u : Rˣ) {n : ℕ} (hi : i < n) (hj : j < n) :
    toStableGL R (h hij u) = StableGeneralLinearGroup.of R n
      (diagGL (Pi.mulSingle (⟨i, hi⟩ : Fin n) u * Pi.mulSingle (⟨j, hj⟩ : Fin n) u⁻¹)) := by
  have hij' : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := fun e ↦ hij (congrArg Fin.val e)
  rw [← toGL_h hij', ← toStableGL_ofFin, ofFin_h]

end SteinbergGroup

namespace IndexedSteinbergGroup

variable {ι R : Type*} [CommRing R]

/-- `x_{ij}(c) = x_{ji}(c⁻¹) w_{ij}(c) x_{ji}(c⁻¹)`, in the presence of a third index `k`. -/
private theorem x_eq_x_mul_w_mul_x {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (c : Rˣ) :
    x hij (c : R) = x hij.symm ((c⁻¹ : Rˣ) : R) * w hij c * x hij.symm ((c⁻¹ : Rˣ) : R) := by
  rw [← w_symm_neg_inv hij hik hjk, w_def]
  simp only [Units.val_neg, inv_neg, inv_inv, neg_neg, ← x_inv]
  group

/-- **A product formula for Weyl elements.** Over a commutative ring, if `u + v = 1` for units
`u` and `v`, then `w_{ij}(u) w_{ij}(v) = w_{ij}(u v⁻¹) w_{ij}(1)`, in the presence of a third index
`k`. -/
theorem w_mul_w_of_add_eq_one {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {u v : Rˣ}
    (huv : (u : R) + v = 1) : w hij u * w hij v = w hij (u * v⁻¹) * w hij 1 := by
  have hu : (u : R) * (u⁻¹ : Rˣ) = 1 := u.mul_inv
  have hv : (v : R) * (v⁻¹ : Rˣ) = 1 := v.mul_inv
  -- Moving `x_{ji}(a)` to the left across `w_{ij}(c)`.
  have hmove (c : Rˣ) (a : R) : w hij c * x hij.symm a = x hij (-((c : R) * a * c)) * w hij c :=
    mul_inv_eq_iff_eq_mul.mp (w_mul_x_mul_inv_ji hij hik hjk c a)
  -- Both sides, multiplied by `P` on the left and `Q` on the right, give `x_{ij}(1)`.
  set P := x hij.symm ((u⁻¹ : Rˣ) : R) * x hij (-((u : R) * ((u⁻¹ : Rˣ) + (v⁻¹ : Rˣ)) * u))
  set Q := x hij.symm ((v⁻¹ : Rˣ) : R)
  have hone : x hij (1 : R) = x hij.symm 1 * x hij (-1) * w hij 1 := by
    rw [← Units.val_one, x_eq_x_mul_w_mul_x hij hik hjk 1, mul_assoc _ (w hij 1), hmove]
    simp [mul_assoc]
  have hL : P * (w hij u * w hij v) * Q = x hij (1 : R) := by
    calc P * (w hij u * w hij v) * Q
        = x hij.symm ((u⁻¹ : Rˣ) : R) *
            (x hij (-((u : R) * (((u⁻¹ : Rˣ) : R) + ((v⁻¹ : Rˣ) : R)) * u)) * w hij u) *
              w hij v * Q := by simp only [P, mul_assoc]
      _ = x hij.symm ((u⁻¹ : Rˣ) : R) *
            (w hij u * x hij.symm (((u⁻¹ : Rˣ) : R) + ((v⁻¹ : Rˣ) : R))) *
            w hij v * x hij.symm ((v⁻¹ : Rˣ) : R) := by rw [hmove]
      _ = x hij (u : R) * x hij (v : R) := by
        rw [x_eq_x_mul_w_mul_x hij hik hjk u, x_eq_x_mul_w_mul_x hij hik hjk v, x_add]
        group
      _ = x hij (1 : R) := by rw [← x_add, huv]
  have hR : P * (w hij (u * v⁻¹) * w hij 1) * Q = x hij (1 : R) := by
    have h₁ : (u : R) * ((u⁻¹ : Rˣ) + (v⁻¹ : Rˣ)) * u = u * (v⁻¹ : Rˣ) := by
      linear_combination (u : R) * hu + (u : R) * (v⁻¹ : Rˣ) * huv - (u : R) * hv
    have h₂ : ((u⁻¹ : Rˣ) : R) + -((v : R) * (u⁻¹ : Rˣ)) = 1 := by
      linear_combination hu - ((u⁻¹ : Rˣ) : R) * huv
    have h₃ : (u : R) * (v⁻¹ : Rˣ) + -(1 * ((v⁻¹ : Rˣ) : R) * 1) = -1 := by
      linear_combination ((v⁻¹ : Rˣ) : R) * huv - hv
    calc P * (w hij (u * v⁻¹) * w hij 1) * Q
        = x hij.symm ((u⁻¹ : Rˣ) : R) * x hij (-((u : R) * (v⁻¹ : Rˣ))) *
            (x hij ((u : R) * (v⁻¹ : Rˣ)) * x hij.symm (-((v : R) * (u⁻¹ : Rˣ))) *
              x hij ((u : R) * (v⁻¹ : Rˣ)) * w hij 1) * x hij.symm ((v⁻¹ : Rˣ) : R) := by
          simp [P, Q, h₁, w_def]
      _ = x hij.symm ((u⁻¹ : Rˣ) : R) * x hij.symm (-((v : R) * (u⁻¹ : Rˣ))) *
            x hij ((u : R) * (v⁻¹ : Rˣ)) * (w hij 1 * x hij.symm ((v⁻¹ : Rˣ) : R)) := by
          rw [← x_inv]
          group
      _ = x hij.symm (((u⁻¹ : Rˣ) : R) + -((v : R) * (u⁻¹ : Rˣ))) *
            x hij ((u : R) * (v⁻¹ : Rˣ) + -(1 * ((v⁻¹ : Rˣ) : R) * 1)) * w hij 1 := by
          rw [hmove, Units.val_one, x_add, x_add]
          group
      _ = x hij.symm 1 * x hij (-1) * w hij 1 := by rw [h₂, h₃]
      _ = x hij (1 : R) := hone.symm
  exact mul_left_cancel (mul_right_cancel (hL.trans hR.symm))

/-- Over a commutative ring, if `u + v = 1` for units `u` and `v`, then
`h_{ij}(u) h_{ij}(v⁻¹) = h_{ij}(u v⁻¹)`, in the presence of a third index `k`. -/
theorem h_mul_h_inv_of_add_eq_one {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {u v : Rˣ} (huv : (u : R) + v = 1) : h hij u * h hij v⁻¹ = h hij (u * v⁻¹) := by
  have key := w_mul_w_of_add_eq_one hij hik hjk huv
  have hneg : (h hij (-v))⁻¹ = h hij v⁻¹ * (h hij (-1))⁻¹ := by
    rw [← h_neg_mul_h_inv hij hik hjk v]
    group
  rw [w_mul_w, w_mul_w, hneg, ← mul_assoc] at key
  exact mul_right_cancel key

/-- **The Steinberg relation in the form `{u, v⁻¹} = 1`**, in the Steinberg group of a commutative
ring: if `u + v = 1` for units `u` and `v`, the diagonal elements `h_{ij}(u)` and `h_{ik}(v⁻¹)`
commute, for pairwise distinct `i, j, k`. -/
theorem commutatorElement_h_h_inv_of_add_eq_one {i j k : ι} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) {u v : Rˣ} (huv : (u : R) + v = 1) : ⁅h hij u, h hik v⁻¹⁆ = 1 := by
  rw [commutatorElement_h_h hij hik hjk, mul_comm v⁻¹ u, h_mul_h_inv_of_add_eq_one hij hik hjk huv,
    mul_inv_cancel]

/-- Over a commutative ring, the images in `GL ι R` of any two diagonal elements commute. -/
theorem toGL_commutatorElement_h_h [Fintype ι] [DecidableEq ι] {i j k l : ι} (hij : i ≠ j)
    (hkl : k ≠ l) (u v : Rˣ) : toGL ⁅h hij u, h hkl v⁆ = 1 := by
  rw [map_commutatorElement, toGL_h, toGL_h, ← map_commutatorElement,
    commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _), map_one]

end IndexedSteinbergGroup

/-! ### Symbols in the stable Steinberg group -/

namespace SteinbergGroup

open IndexedSteinbergGroup

variable {R : Type*} [CommRing R]

/-- Over a commutative ring, the commutator of two diagonal elements of `St(R)` lies in the kernel
`K₂(R)` of `St(R) → GL_∞(R)`. -/
theorem commutatorElement_h_h_mem_ker {i j k l : ℕ} (hij : i ≠ j) (hkl : k ≠ l) (u v : Rˣ) :
    ⁅h hij u, h hkl v⁆ ∈ (toStableGL R).ker := by
  set n := max (max i j) (max k l) + 1
  rw [MonoidHom.mem_ker, map_commutatorElement, toStableGL_h hij u (n := n) (by omega) (by omega),
    toStableGL_h hkl v (n := n) (by omega) (by omega), ← map_commutatorElement,
    ← map_commutatorElement, commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _), map_one,
    map_one]

/-- Over a commutative ring, the commutator of two diagonal elements of `St(R)` is central. -/
theorem commutatorElement_h_h_mem_center {i j k l : ℕ} (hij : i ≠ j) (hkl : k ≠ l) (u v : Rˣ) :
    ⁅h hij u, h hkl v⁆ ∈ Subgroup.center (SteinbergGroup R) :=
  ker_toStableGL_le_center (commutatorElement_h_h_mem_ker hij hkl u v)

/-- **Bimultiplicativity of symbols, left variable.** Over a commutative ring and for pairwise
distinct `i, j, k`, `⁅h_{ij}(u u'), h_{ik}(v)⁆ = ⁅h_{ij}(u), h_{ik}(v)⁆ ⁅h_{ij}(u'), h_{ik}(v)⁆`
in `St(R)`. -/
theorem commutatorElement_h_h_mul_left {i j k : ℕ} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u u' v : Rˣ) :
    ⁅h hij (u * u'), h hik v⁆ = ⁅h hij u, h hik v⁆ * ⁅h hij u', h hik v⁆ := by
  have hc := commutatorElement_h_h_mem_center hij hik u u'
  have hmul : h hij (u * u') = h hij u * h hij u' * ⁅h hij u, h hik u'⁆⁻¹ := by
    rw [Subgroup.mem_center_iff.mp (inv_mem hc), commutatorElement_h_h hij hik hjk, mul_comm u' u]
    group
  have hdrop := commutatorElement_mul_mul_of_mem_center (a := h hij u * h hij u') (c := h hik v)
    (inv_mem hc) (one_mem _)
  rw [mul_one] at hdrop
  rw [hmul, hdrop, commutatorElement_mul_left_eq_conj_mul,
    Subgroup.mem_center_iff.mp (commutatorElement_h_h_mem_center hij hik u' v) (h hij u),
    mul_inv_cancel_right,
    Subgroup.mem_center_iff.mp (commutatorElement_h_h_mem_center hij hik u v)]

/-- **Bimultiplicativity of symbols, right variable.** Over a commutative ring and for pairwise
distinct `i, j, k`, `⁅h_{ij}(u), h_{ik}(v v')⁆ = ⁅h_{ij}(u), h_{ik}(v)⁆ ⁅h_{ij}(u), h_{ik}(v')⁆`
in `St(R)`. -/
theorem commutatorElement_h_h_mul_right {i j k : ℕ} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u v v' : Rˣ) :
    ⁅h hij u, h hik (v * v')⁆ = ⁅h hij u, h hik v⁆ * ⁅h hij u, h hik v'⁆ := by
  have hc := commutatorElement_h_h_mem_center hik hij v v'
  have hmul : h hik (v * v') = h hik v * h hik v' * ⁅h hik v, h hij v'⁆⁻¹ := by
    rw [Subgroup.mem_center_iff.mp (inv_mem hc), commutatorElement_h_h hik hij hjk.symm,
      mul_comm v' v]
    group
  have hdrop := commutatorElement_mul_mul_of_mem_center (a := h hij u) (c := h hik v * h hik v')
    (one_mem _) (inv_mem hc)
  rw [mul_one] at hdrop
  rw [hmul, hdrop, commutatorElement_mul_right_eq_mul_conj, mul_assoc _ (h hik v),
    Subgroup.mem_center_iff.mp (commutatorElement_h_h_mem_center hij hik u v') (h hik v),
    ← mul_assoc, mul_inv_cancel_right]

/-- **The Steinberg relation `{u, v} = 1` for `u + v = 1`.** Over a commutative ring, if `u + v = 1`
for units `u` and `v`, then `h_{ij}(u)` and `h_{ik}(v)` commute in `St(R)`, for pairwise distinct
`i, j, k`. -/
theorem commutatorElement_h_h_of_add_eq_one {i j k : ℕ} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {u v : Rˣ} (huv : (u : R) + v = 1) : ⁅h hij u, h hik v⁆ = 1 := by
  have key := commutatorElement_h_h_mul_right hij hik hjk u v v⁻¹
  rwa [mul_inv_cancel, h_one, commutatorElement_one_right,
    commutatorElement_h_h_inv_of_add_eq_one hij hik hjk huv, mul_one, eq_comm] at key

/-- **The relation `{u, -u} = 1`.** Over a commutative ring, `h_{ij}(u)` and `h_{ik}(-u)` commute
in `St(R)`, for pairwise distinct `i, j, k`. -/
theorem commutatorElement_h_h_neg {i j k : ℕ} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) : ⁅h hij u, h hik (-u)⁆ = 1 := by
  have key := commutatorElement_h_h_mul_left hij hik hjk u⁻¹ u (-u)
  have hneg := commutatorElement_h_neg_h_inv hij hik hjk (-u⁻¹)
  rw [neg_neg, inv_neg, inv_inv] at hneg
  rwa [inv_mul_cancel, h_one, commutatorElement_one_left, hneg, one_mul, eq_comm] at key

end SteinbergGroup

end TauCeti
