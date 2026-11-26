/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.Basic

/-!
# Weyl and diagonal lift words in the Steinberg group

For an associative unital ring `R`, distinct indices `i ≠ j` and a unit `u : Rˣ`, the **Weyl lift
word** `w_{ij}(u) = x_{ij}(u) x_{ji}(-u⁻¹) x_{ij}(u)` of the Steinberg group `St_ι(R)` lifts the
monomial matrix agreeing with the identity off the coordinates `i, j` and having entries `u` at
`(i, j)` and `-u⁻¹` at `(j, i)`. The **diagonal lift word** `h_{ij}(u) = w_{ij}(u) w_{ij}(-1)` lifts
the diagonal matrix with entries `u` at `i` and `u⁻¹` at `j`. These words are the basic tools of
Milnor's matrix calculus of `K₂`; for instance the Steinberg symbol `{u, v}` is the commutator
`⁅h₀₁(u), h₀₂(v)⁆` (`TauCeti.coe_steinbergSymbol_eq_commutatorElement_h`).

Conjugation by `w_{ij}(u)` permutes the root subgroups like the monomial matrix it lifts: writing
`σ` for the transposition of `i` and `j` and `v` for the family of units with `v_i = -u⁻¹`,
`v_j = u` and `v_k = 1` otherwise, `w_{ij}(u) x_{kl}(t) w_{ij}(u)⁻¹ = x_{σk, σl}(v_k t v_l⁻¹)`.
For the roots `(i, j)` and `(j, i)` this needs a third index, since `St₂(R)` is a free product
(`TauCeti.IndexedSteinbergGroup.finTwoEquivCoprod`). Likewise, with `d_i = u`, `d_j = u⁻¹` and
`d_k = 1` otherwise, `h_{ij}(u) x_{kl}(t) h_{ij}(u)⁻¹ = x_{kl}(d_k t d_l⁻¹)`.

## Main definitions

* `TauCeti.IndexedSteinbergGroup.w`: the Weyl lift word `w_{ij}(u)`.
* `TauCeti.IndexedSteinbergGroup.h`: the diagonal lift word `h_{ij}(u) = w_{ij}(u) w_{ij}(-1)`.

## Main results

* `TauCeti.IndexedSteinbergGroup.toGL_w`, `TauCeti.IndexedSteinbergGroup.toGL_h`: the images of
  `w_{ij}(u)` and `h_{ij}(u)` in `GL ι R` are the permutation matrix of `(i j)` times
  `diag(v)`, and `diag(d)`.
* `TauCeti.IndexedSteinbergGroup.w_mul_x_mul_inv`,
  `TauCeti.IndexedSteinbergGroup.h_mul_x_mul_inv`: conjugation of the root generators by `w_{ij}(u)`
  and `h_{ij}(u)`.
* `TauCeti.IndexedSteinbergGroup.commute_w_x`: `w_{ij}(u)` commutes with `x_{kl}(t)` when
  `{k, l}` is disjoint from `{i, j}`.
* `TauCeti.IndexedSteinbergGroup.w_inv`, `TauCeti.IndexedSteinbergGroup.w_symm`:
  `w_{ij}(u)⁻¹ = w_{ij}(-u)` and, given a third index, `w_{ji}(u) = w_{ij}(-u⁻¹)`.
* `TauCeti.IndexedSteinbergGroup.map_w`, `TauCeti.IndexedSteinbergGroup.mapIndex_w`,
  `TauCeti.SteinbergGroup.ofFin_w` and their analogues for `h`: naturality in ring homomorphisms,
  index embeddings and stabilization.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §9,
  Lemma 9.2 and Corollary 9.3.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, 5.10.1 and Exercise 5.8.
-/

public section

noncomputable section

open scoped commutatorElement

namespace TauCeti

namespace IndexedSteinbergGroup

variable {ι R : Type*} [Ring R]

/-! ## The Weyl lift words -/

/-- The **Weyl lift word** `w_{ij}(u) = x_{ij}(u) x_{ji}(-u⁻¹) x_{ij}(u)` of the Steinberg group,
for distinct indices `i ≠ j` and a unit `u`. It lifts the monomial matrix with entries `u` at
`(i, j)` and `-u⁻¹` at `(j, i)` (`TauCeti.IndexedSteinbergGroup.toGL_w`). -/
def w {i j : ι} (hij : i ≠ j) (u : Rˣ) : IndexedSteinbergGroup ι R :=
  x hij (u : R) * x hij.symm (-(↑u⁻¹ : R)) * x hij (u : R)

/-- Unfolding lemma for the Weyl lift word `w_{ij}(u)`. -/
theorem w_def {i j : ι} (hij : i ≠ j) (u : Rˣ) :
    w hij u = x hij (u : R) * x hij.symm (-(↑u⁻¹ : R)) * x hij (u : R) :=
  (rfl)

private theorem conj_w {i j : ι} (hij : i ≠ j) (u : Rˣ) :
    MulAut.conj (w hij u) = MulAut.conj (x hij (u : R)) *
      MulAut.conj (x hij.symm (-(↑u⁻¹ : R))) * MulAut.conj (x hij (u : R)) := by
  simp [w]

private theorem conj_x_of_commute {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (a b : R) : MulAut.conj (x hij a) (x hkl b) = x hkl b := by
  rw [MulAut.conj_apply, (commute_x hij hkl hjk hli a b).eq, mul_inv_cancel_right]

private theorem conj_x_chain {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    MulAut.conj (x hij a) (x hjk b) = x hik (a * b) * x hjk b :=
  x_mul_x_mul_inv hij hjk hik a b

private theorem conj_x_chain_reverse {i j k : ι} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (a b : R) : MulAut.conj (x hij a) (x hki b) = x hkj (-(b * a)) * x hki b :=
  x_mul_x_mul_inv_reverse hij hki hkj a b

private theorem w_conj_ik {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (t : R) : w hij u * x hik t * (w hij u)⁻¹ = x hjk (-(↑u⁻¹ * t)) := by
  rw [← MulAut.conj_apply, conj_w, MulAut.mul_apply, MulAut.mul_apply,
    conj_x_of_commute hij hik hij.symm hik.symm, conj_x_chain hij.symm hik hjk, map_mul,
    conj_x_chain hij hjk hik, conj_x_of_commute hij hik hij.symm hik.symm, mul_assoc,
    (commute_x hjk hik hik.symm hjk.symm _ _).eq, ← mul_assoc, ← x_add]
  simp

/-- The inverse of a Weyl lift word negates its unit: `w_{ij}(u)⁻¹ = w_{ij}(-u)`. -/
@[simp]
theorem w_inv {i j : ι} (hij : i ≠ j) (u : Rˣ) : (w hij u)⁻¹ = w hij (-u) := by
  simp [w, mul_assoc]

private theorem w_conj_jk {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (t : R) : w hij u * x hjk t * (w hij u)⁻¹ = x hik (u * t) := by
  have h := w_conj_ik hij hik hjk (-u) (u * t)
  rw [← w_inv, inv_inv, show -(↑(-u)⁻¹ * (↑u * t)) = t by simp] at h
  rw [← h]
  group

private theorem w_conj_ki {i j k : ι} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (u : Rˣ)
    (t : R) : w hij u * x hki t * (w hij u)⁻¹ = x hkj (-(t * u)) := by
  rw [← MulAut.conj_apply, conj_w, MulAut.mul_apply, MulAut.mul_apply,
    conj_x_chain_reverse hij hki hkj, map_mul, map_mul, conj_x_chain_reverse hij.symm hkj hki,
    conj_x_of_commute hij.symm hki hki.symm hij]
  simp only [map_mul, conj_x_chain_reverse hij hki hkj,
    conj_x_of_commute hij hkj hkj.symm hij.symm]
  have hc := commute_x (R := R) hki hkj hki.symm hkj.symm
  rw [mul_assoc, mul_assoc, (hc _ _).left_comm, (hc _ _).left_comm, ← x_add hki,
    ← mul_assoc, ← mul_assoc, ← x_add hkj, ← x_add hkj]
  simp [mul_assoc]

private theorem w_conj_kj {i j k : ι} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (u : Rˣ)
    (t : R) : w hij u * x hkj t * (w hij u)⁻¹ = x hki (t * ↑u⁻¹) := by
  have h := w_conj_ki hij hki hkj (-u) (t * ↑u⁻¹)
  rw [← w_inv, inv_inv, show -(t * ↑u⁻¹ * ↑(-u)) = t by simp] at h
  rw [← h]
  group

private theorem w_conj_ij {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (t : R) : w hij u * x hij t * (w hij u)⁻¹ = x hij.symm (-(↑u⁻¹ * t * ↑u⁻¹)) := by
  rw [← MulAut.conj_apply, ← mul_one t, ← commutatorElement_x hik hjk.symm hij,
    map_commutatorElement, MulAut.conj_apply, MulAut.conj_apply, w_conj_ik hij hik hjk,
    w_conj_kj hij hik.symm hjk.symm, commutatorElement_x hjk hik.symm hij.symm]
  simp [mul_assoc]

private theorem w_conj_ji {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (t : R) : w hij u * x hij.symm t * (w hij u)⁻¹ = x hij (-(↑u * t * ↑u)) := by
  rw [← MulAut.conj_apply, ← mul_one t, ← commutatorElement_x hjk hik.symm hij.symm,
    map_commutatorElement, MulAut.conj_apply, MulAut.conj_apply,
    w_conj_jk hij hik hjk, w_conj_ki hij hik.symm hjk.symm,
    commutatorElement_x hik hjk.symm hij]
  simp [mul_assoc]

/-- `w_{ij}(u)` commutes with every root generator `x_{kl}(t)` with `{k, l}` disjoint from
`{i, j}`. -/
theorem commute_w_x {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hjk : j ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (u : Rˣ) (t : R) : Commute (w hij u) (x hkl t) := by
  rw [commute_iff_eq, ← mul_inv_eq_iff_eq_mul, ← MulAut.conj_apply, conj_w]
  simp only [MulAut.mul_apply, conj_x_of_commute hij hkl hjk hil.symm,
    conj_x_of_commute hij.symm hkl hik hjl.symm]

/-- **The two Weyl lift words of a pair of opposite roots agree**: if some index lies outside
`{i, j}`, then `w_{ji}(u) = w_{ij}(-u⁻¹)`. -/
theorem w_symm {i j : ι} (hij : i ≠ j) (h3 : ∃ m, m ≠ i ∧ m ≠ j) (u : Rˣ) :
    w hij.symm u = w hij (-u⁻¹) := by
  obtain ⟨k, hki, hkj⟩ := h3
  set v : Rˣ := -u⁻¹ with hv
  have hu : u = -v⁻¹ := by simp [hv]
  rw [hu]
  have h := w_conj_ji hij hki.symm hkj.symm v (-(↑v⁻¹ : R))
  rw [show -(↑v * -(↑v⁻¹ : R) * ↑v) = (v : R) by simp, mul_inv_eq_iff_eq_mul, w] at h
  have hw : w hij.symm (-v⁻¹) =
      x hij.symm (-(↑v⁻¹ : R)) * x hij (v : R) * x hij.symm (-(↑v⁻¹ : R)) := by
    simp [w]
  rw [hw, w]
  refine (mul_left_cancel (a := x hij (v : R)) ?_).symm
  simpa only [mul_assoc] using h.symm

private theorem x_eq_x {i j i' j' : ι} (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i') (hj : j = j')
    {a a' : R} (ha : a = a') : x hij a = x hij' a' := by
  subst hi hj ha
  rfl

/-- **Conjugation by a Weyl lift word permutes the root generators.** Let `σ` be the
transposition of `i` and `j`, and let `v` be the family of units with `v_i = -u⁻¹`, `v_j = u` and
`v_k = 1` otherwise, so that `w_{ij}(u)` lifts the monomial matrix `P_σ diag(v)`. If some index lies
outside `{i, j}`, then `w_{ij}(u) x_{kl}(t) w_{ij}(u)⁻¹ = x_{σk, σl}(v_k t v_l⁻¹)`. -/
theorem w_mul_x_mul_inv [DecidableEq ι] {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (h3 : ∃ m, m ≠ i ∧ m ≠ j) (u : Rˣ) (t : R) :
    w hij u * x hkl t * (w hij u)⁻¹ =
      x ((Equiv.swap i j).injective.ne hkl)
        ((Pi.mulSingle i (-u⁻¹) * Pi.mulSingle j u : ι → Rˣ) k * t *
          ↑((Pi.mulSingle i (-u⁻¹) * Pi.mulSingle j u : ι → Rˣ) l)⁻¹) := by
  obtain ⟨m, hmi, hmj⟩ := h3
  rcases eq_or_ne k i with rfl | hki
  · rcases eq_or_ne l j with rfl | hlj
    · rw [w_conj_ij hij hmi.symm hmj.symm]
      exact x_eq_x _ _ (by simp) (by simp) (by simp [hij, mul_assoc])
    · rw [w_conj_ik hij hkl hlj.symm]
      exact x_eq_x _ _ (by simp) (by simp [Equiv.swap_apply_of_ne_of_ne hkl.symm hlj])
        (by simp [hij, hkl.symm, hlj])
  rcases eq_or_ne k j with rfl | hkj
  · rcases eq_or_ne l i with rfl | hli
    · rw [w_conj_ji hij hmi.symm hmj.symm]
      exact x_eq_x _ _ (by simp) (by simp) (by simp [hij, mul_assoc])
    · rw [w_conj_jk hij hli.symm hkl]
      exact x_eq_x _ _ (by simp) (by simp [Equiv.swap_apply_of_ne_of_ne hli hkl.symm])
        (by simp [hij.symm, hli, hkl.symm])
  rcases eq_or_ne l i with rfl | hli
  · rw [w_conj_ki hij hki hkj]
    exact x_eq_x _ _ (by simp [Equiv.swap_apply_of_ne_of_ne hki hkj]) (by simp)
      (by simp [hki, hkj, hij])
  rcases eq_or_ne l j with rfl | hlj
  · rw [w_conj_kj hij hki hkj]
    exact x_eq_x _ _ (by simp [Equiv.swap_apply_of_ne_of_ne hki hkj]) (by simp)
      (by simp [hki, hkj, hij.symm])
  rw [(commute_w_x hij hkl hki.symm hkj.symm hli.symm hlj.symm u t).eq, mul_inv_cancel_right]
  exact x_eq_x _ _ (by simp [Equiv.swap_apply_of_ne_of_ne hki hkj])
    (by simp [Equiv.swap_apply_of_ne_of_ne hli hlj]) (by simp [hki, hkj, hli, hlj])

/-! ## The diagonal lift words -/

/-- The **diagonal lift word** `h_{ij}(u) = w_{ij}(u) w_{ij}(-1)` of the Steinberg group, for
distinct indices `i ≠ j` and a unit `u`. It lifts the diagonal matrix with entries `u` at `i` and
`u⁻¹` at `j` (`TauCeti.IndexedSteinbergGroup.toGL_h`). -/
def h {i j : ι} (hij : i ≠ j) (u : Rˣ) : IndexedSteinbergGroup ι R :=
  w hij u * w hij (-1)

/-- Unfolding lemma for the diagonal lift word `h_{ij}(u)`. -/
theorem h_def {i j : ι} (hij : i ≠ j) (u : Rˣ) : h hij u = w hij u * w hij (-1) :=
  (rfl)

/-- The diagonal lift word of the unit `1` is trivial. -/
@[simp]
theorem h_one {i j : ι} (hij : i ≠ j) : h hij (1 : Rˣ) = 1 := by
  rw [h_def, ← w_inv, mul_inv_cancel]

private theorem mulSingle_swap_mul_mulSingle [DecidableEq ι] {i j : ι} (hij : i ≠ j) (u : Rˣ)
    (m : ι) :
    (Pi.mulSingle i (-u⁻¹) * Pi.mulSingle j u : ι → Rˣ) (Equiv.swap i j m) *
        (Pi.mulSingle i (-(-1)⁻¹) * Pi.mulSingle j (-1) : ι → Rˣ) m =
      (Pi.mulSingle i u * Pi.mulSingle j u⁻¹ : ι → Rˣ) m := by
  rcases eq_or_ne m i with rfl | hmi
  · simp [hij, hij.symm]
  rcases eq_or_ne m j with rfl | hmj
  · simp [hij, hij.symm]
  simp [Equiv.swap_apply_of_ne_of_ne hmi hmj, hmi, hmj]

/-- **Conjugation by a diagonal lift word rescales the root generators.** Let `d` be the family of
units with `d_i = u`, `d_j = u⁻¹` and `d_k = 1` otherwise, so that `h_{ij}(u)` lifts `diag(d)`. If
some index lies outside `{i, j}`, then `h_{ij}(u) x_{kl}(t) h_{ij}(u)⁻¹ = x_{kl}(d_k t d_l⁻¹)`. -/
theorem h_mul_x_mul_inv [DecidableEq ι] {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (h3 : ∃ m, m ≠ i ∧ m ≠ j) (u : Rˣ) (t : R) :
    h hij u * x hkl t * (h hij u)⁻¹ =
      x hkl ((Pi.mulSingle i u * Pi.mulSingle j u⁻¹ : ι → Rˣ) k * t *
        ↑((Pi.mulSingle i u * Pi.mulSingle j u⁻¹ : ι → Rˣ) l)⁻¹) := by
  rw [h_def, mul_inv_rev, show ∀ a b c d : IndexedSteinbergGroup ι R,
    a * b * c * (d * a⁻¹) = a * (b * c * d) * a⁻¹ from fun _ _ _ _ ↦ by group,
    w_mul_x_mul_inv hij hkl h3, w_mul_x_mul_inv hij _ h3]
  refine x_eq_x _ _ (by simp) (by simp) ?_
  rw [← mulSingle_swap_mul_mulSingle hij u k, ← mulSingle_swap_mul_mulSingle hij u l]
  simp only [Units.val_mul, mul_inv_rev, mul_assoc]

/-! ## Naturality -/

section Functoriality

variable {κ S : Type*} [Ring S]

/-- Ring homomorphisms preserve the Weyl lift words. -/
@[simp]
theorem map_w (f : R →+* S) {i j : ι} (hij : i ≠ j) (u : Rˣ) :
    map f (w hij u) = w hij (Units.map (f : R →* S) u) := by
  simp [w, map_x]

/-- Ring homomorphisms preserve the diagonal lift words. -/
@[simp]
theorem map_h (f : R →+* S) {i j : ι} (hij : i ≠ j) (u : Rˣ) :
    map f (h hij u) = h hij (Units.map (f : R →* S) u) := by
  simp [h_def]

/-- Index embeddings preserve the Weyl lift words. -/
@[simp]
theorem mapIndex_w (e : ι ↪ κ) {i j : ι} (hij : i ≠ j) (u : Rˣ) :
    mapIndex e (w hij u) = w (e.injective.ne hij) u := by
  simp [w]

/-- Index embeddings preserve the diagonal lift words. -/
@[simp]
theorem mapIndex_h (e : ι ↪ κ) {i j : ι} (hij : i ≠ j) (u : Rˣ) :
    mapIndex e (h hij u) = h (e.injective.ne hij) u := by
  simp [h_def]

end Functoriality


/-! ## Images in the general linear group -/

section toGL

variable [Fintype ι] [DecidableEq ι]

/-- The image of `w_{ij}(u)` in `GL ι R` is the monomial matrix `P_σ diag(v)`, where `σ` is the
transposition of `i` and `j`, `v_i = -u⁻¹`, `v_j = u` and `v_k = 1` otherwise: it has entries `u` at
`(i, j)` and `-u⁻¹` at `(j, i)`, and agrees with the identity off the coordinates `i, j`. -/
@[simp]
theorem toGL_w {i j : ι} (hij : i ≠ j) (u : Rˣ) :
    toGL (w hij u) = permutationGL (Equiv.swap i j) *
      diagGL (Pi.mulSingle i (-u⁻¹) * Pi.mulSingle j u) := by
  have hL : (toGL (w hij u) : Matrix ι ι R) = 1 + Matrix.single i j (u : R) +
      Matrix.single j i (-(↑u⁻¹ : R)) + Matrix.single i i (-1) + Matrix.single j j (-1) := by
    simp only [w, map_mul, toGL_x, Units.val_mul, coe_transvectionUnit_eq_one_add_single,
      add_mul, mul_add, one_mul, mul_one]
    simp only [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
      Units.mul_inv, Units.inv_mul, mul_neg, neg_mul, one_mul, add_zero, ← Matrix.single_neg]
    abel
  ext a b
  rw [hL, Units.val_mul, permutationGL_coe, diagGL_coe, Matrix.mul_diagonal]
  simp only [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Equiv.swap_inv, Pi.mul_apply,
    Units.val_mul]
  clear hL
  by_cases hia : i = a <;> by_cases hja : j = a <;> by_cases hib : i = b <;>
    by_cases hjb : j = b <;> simp_all [Equiv.swap_apply_def, eq_comm]

/-- The image of `h_{ij}(u)` in `GL ι R` is the diagonal matrix with entries `u` at `i`, `u⁻¹` at
`j` and `1` elsewhere. -/
@[simp]
theorem toGL_h {i j : ι} (hij : i ≠ j) (u : Rˣ) :
    toGL (h hij u) = diagGL (Pi.mulSingle i u * Pi.mulSingle j u⁻¹) := by
  rw [h_def, map_mul, toGL_w, toGL_w, ← mul_assoc]
  ext a b
  rw [Units.val_mul _ (diagGL _), diagGL_coe, Matrix.mul_diagonal, coe_mul_permutationGL_apply,
    Units.val_mul, permutationGL_coe, diagGL_coe, Matrix.mul_diagonal, diagGL_coe,
    Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left rfl, ← mulSingle_swap_mul_mulSingle hij u a, Units.val_mul]
    simp [PEquiv.toMatrix_apply]
  · simp [PEquiv.toMatrix_apply, hab]

end toGL

end IndexedSteinbergGroup

namespace SteinbergGroup

open IndexedSteinbergGroup

variable {R : Type*} [Ring R]

/-- Stabilization `Stₙ(R) →* St(R)` sends Weyl lift words to Weyl lift words. -/
@[simp]
theorem ofFin_w {n : ℕ} {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    ofFin R n (w hij u) = w (Fin.val_ne_of_ne hij) u := by
  simp [w_def]

/-- Stabilization `Stₙ(R) →* St(R)` sends diagonal lift words to diagonal lift words. -/
@[simp]
theorem ofFin_h {n : ℕ} {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    ofFin R n (h hij u) = h (Fin.val_ne_of_ne hij) u := by
  simp [h_def]

end SteinbergGroup

end TauCeti
