/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.WittVector.Basic

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.Algebra.Ring.FrobeniusLift

/-!
# Ramified ghost components and the ramified Dwork criterion

Let `O` be a commutative ring, `π ∈ O` and `q` a natural number. In the main application `O` is
the ring of integers of a nonarchimedean local field, `π` is a uniformizer and `q` is the
cardinality of the residue field. For an `O`-algebra `A`, the `n`-th ramified ghost component of a
sequence `x : ℕ → A` is

`w_n(x) = ∑_{i ≤ n} π ^ i * x_i ^ (q ^ (n - i))`.

These are the ghost components of the ramified Witt vectors `W_O(A)` of Fargues and Fontaine, and
for `π = q = p` they are the ghost components of Mathlib's `p`-typical Witt vectors. They are the
evaluations of the ramified Witt polynomials `ramifiedWittPolynomial π q n`, and they are natural in
the `O`-algebra `A`.

The ramified Dwork criterion describes the ghost image. Suppose `π ∣ q` in `A` and `σ` is an
`O`-algebra endomorphism of `A` lifting `a ↦ a ^ q` modulo `π`. Then a sequence `y` is the sequence
of ghost components of some `x` exactly when `y (n + 1) ≡ σ (y n)` modulo `π ^ (n + 1)` for every
`n`. No completeness of `A` is needed, and neither is torsion-freeness. When `π` is moreover a
nonzerodivisor of `A`, the ghost map is injective, so each such `y` has exactly one preimage.
Torsion-freeness cannot be dropped from injectivity: if `π` maps to `0`, as in the residue field,
then `w_n(x) = x_0 ^ (q ^ n)` forgets every coordinate but the first.

## Main definitions

* `TauCeti.ramifiedGhost π q n x`: the ramified ghost component `w_n(x)`.
* `TauCeti.ramifiedWittPolynomial π q n`: the polynomial `∑_{i ≤ n} π ^ i X_i ^ (q ^ (n - i))`.

## Main results

* `TauCeti.ramifiedGhost_succ`: `w_{n+1}(x) = w_n(x ^ q) + π ^ (n + 1) x_{n+1}`.
* `TauCeti.map_ramifiedGhost`: ghost components commute with `O`-algebra maps.
* `TauCeti.aeval_ramifiedWittPolynomial`: `w_n` is the evaluation of the ramified Witt polynomial.
* `TauCeti.ramifiedGhost_natCast_self_coeff`: for `π = q = p` the ramified ghost components of
  the coordinates of a `p`-typical Witt vector are its `WittVector.ghostComponent`s.
* `TauCeti.ramifiedGhost_injective`: the ghost map is injective when `π` is a nonzerodivisor.
* `TauCeti.not_injective_ramifiedGhost_of_algebraMap_eq_zero`: it is not injective when `π` maps
  to `0` in a nontrivial algebra.
* `TauCeti.exists_ramifiedGhost_eq_iff`: the ramified Dwork criterion for the ghost image.
* `TauCeti.exists_ramifiedGhost_natCard_residueField_eq_iff`: the criterion over a local ring
  whose maximal ideal lies in `(π)` and whose residue field is finite, with `q` the cardinality of
  the residue field.
* `TauCeti.WittVector.mem_range_ghostMap_iff` and `TauCeti.WittVector.ghostMap_injective`:
  Dwork's criterion for `p`-typical Witt vectors.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge `p`-adique*,
  Astérisque 406 (2018), §1.2.1 and Lemme 1.2.1.
-/

public section

namespace TauCeti

open Finset MvPolynomial

section Ghost

variable {O : Type*} [CommRing O] {A B : Type*} [CommRing A] [Algebra O A] [CommRing B]
  [Algebra O B]

/-- The `n`-th ramified ghost component `w_n(x) = ∑_{i ≤ n} π ^ i * x_i ^ (q ^ (n - i))` of a
sequence `x` in an `O`-algebra `A`. -/
def ramifiedGhost (π : O) (q n : ℕ) (x : ℕ → A) : A :=
  ∑ i ∈ range (n + 1), algebraMap O A π ^ i * x i ^ q ^ (n - i)

variable {π : O} {q : ℕ}

theorem ramifiedGhost_def (n : ℕ) (x : ℕ → A) :
    ramifiedGhost π q n x = ∑ i ∈ range (n + 1), algebraMap O A π ^ i * x i ^ q ^ (n - i) :=
  (rfl)

@[simp]
theorem ramifiedGhost_zero (x : ℕ → A) : ramifiedGhost π q 0 x = x 0 := by
  simp [ramifiedGhost_def]

/-- The ghost recursion `w_{n+1}(x) = w_n(x ^ q) + π ^ (n + 1) x_{n+1}`. -/
theorem ramifiedGhost_succ (n : ℕ) (x : ℕ → A) :
    ramifiedGhost π q (n + 1) x =
      ramifiedGhost π q n (fun i ↦ x i ^ q) + algebraMap O A π ^ (n + 1) * x (n + 1) := by
  rw [ramifiedGhost_def, sum_range_succ, ramifiedGhost_def, Nat.sub_self, pow_zero, pow_one]
  congr 1
  refine sum_congr rfl fun i hi ↦ ?_
  rw [← pow_mul, ← pow_succ', Nat.sub_add_comm (Nat.lt_succ_iff.1 (mem_range.1 hi))]

@[simp]
theorem ramifiedGhost_one (x : ℕ → A) :
    ramifiedGhost π q 1 x = x 0 ^ q + algebraMap O A π * x 1 := by
  simp [ramifiedGhost_succ]

/-- The ghost component `w_n(x)` only depends on the coordinates `x_0, …, x_n`. -/
theorem ramifiedGhost_congr {n : ℕ} {x y : ℕ → A} (h : ∀ i ≤ n, x i = y i) :
    ramifiedGhost π q n x = ramifiedGhost π q n y :=
  sum_congr rfl fun i hi ↦ by rw [h i (Nat.lt_succ_iff.1 (mem_range.1 hi))]

/-- Ramified ghost components are natural in the coefficient algebra. -/
@[simp]
theorem map_ramifiedGhost (f : A →ₐ[O] B) (n : ℕ) (x : ℕ → A) :
    f (ramifiedGhost π q n x) = ramifiedGhost π q n (fun i ↦ f (x i)) := by
  simp [ramifiedGhost_def]

/-- If `π` maps to `0` in `A`, the ghost components only see the first coordinate:
`w_n(x) = x_0 ^ (q ^ n)`. -/
theorem ramifiedGhost_of_algebraMap_eq_zero (hπ : algebraMap O A π = 0) (n : ℕ) (x : ℕ → A) :
    ramifiedGhost π q n x = x 0 ^ q ^ n := by
  simp [ramifiedGhost_def, sum_range_succ', hπ]

end Ghost

section Polynomial

variable {O : Type*} [CommRing O]

/-- The ramified Witt polynomial `∑_{i ≤ n} π ^ i X_i ^ (q ^ (n - i))` over `O`; its evaluation at
a sequence is the ramified ghost component `ramifiedGhost π q n`. -/
noncomputable def ramifiedWittPolynomial (π : O) (q n : ℕ) : MvPolynomial ℕ O :=
  ∑ i ∈ range (n + 1), C (π ^ i) * X i ^ q ^ (n - i)

theorem ramifiedWittPolynomial_def (π : O) (q n : ℕ) :
    ramifiedWittPolynomial π q n = ∑ i ∈ range (n + 1), C (π ^ i) * X i ^ q ^ (n - i) :=
  (rfl)

@[simp]
theorem aeval_ramifiedWittPolynomial {A : Type*} [CommRing A] [Algebra O A] (π : O) (q n : ℕ)
    (x : ℕ → A) : aeval x (ramifiedWittPolynomial π q n) = ramifiedGhost π q n x := by
  simp [ramifiedWittPolynomial, ramifiedGhost_def]

/-- For `π = q = p` the ramified Witt polynomials are Mathlib's `p`-typical Witt polynomials. -/
theorem ramifiedWittPolynomial_natCast_self (p n : ℕ) :
    ramifiedWittPolynomial (p : O) p n = wittPolynomial p O n := by
  simp [ramifiedWittPolynomial, wittPolynomial_eq_sum_C_mul_X_pow]

/-- For `π = q = p`, the ramified ghost components of the coordinates of a `p`-typical Witt vector
are its ghost components. -/
@[simp]
theorem ramifiedGhost_natCast_self_coeff {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
    [Algebra O R] (x : _root_.WittVector p R) (n : ℕ) :
    ramifiedGhost (p : O) p n x.coeff = _root_.WittVector.ghostComponent n x := by
  simp [_root_.WittVector.ghostComponent_apply, aeval_wittPolynomial, ramifiedGhost_def]

end Polynomial

section Dwork

variable {O : Type*} [CommRing O] {A : Type*} [CommRing A] [Algebra O A] {π : O} {q : ℕ}

/-- If `π` is a nonzerodivisor of `A`, the ghost components `w_0, …, w_n` of a sequence determine
its coordinates `x_0, …, x_n`. -/
theorem eq_of_forall_le_ramifiedGhost_eq (hπ : algebraMap O A π ∈ nonZeroDivisors A) {n : ℕ}
    {x y : ℕ → A} (h : ∀ k ≤ n, ramifiedGhost π q k x = ramifiedGhost π q k y) :
    ∀ k ≤ n, x k = y k := by
  induction n with
  | zero => simpa using h 0 le_rfl
  | succ n ih =>
    have hle := ih fun k hk ↦ h k (hk.trans n.le_succ)
    intro k hk
    rcases Nat.lt_or_eq_of_le hk with hk | rfl
    · exact hle k (Nat.lt_succ_iff.1 hk)
    · -- Cancel the common part `w_n(x ^ q) = w_n(y ^ q)` and then the power `π ^ (n + 1)`.
      have h' := h (n + 1) le_rfl
      rw [ramifiedGhost_succ, ramifiedGhost_succ,
        ramifiedGhost_congr fun i hi ↦ congrArg (· ^ q) (hle i hi), add_right_inj] at h'
      exact (mul_cancel_left_mem_nonZeroDivisors (pow_mem hπ _)).1 h'

/-- If `π` is a nonzerodivisor of `A`, a sequence is determined by its ramified ghost
components. -/
theorem ramifiedGhost_injective (hπ : algebraMap O A π ∈ nonZeroDivisors A) :
    Function.Injective fun (x : ℕ → A) n ↦ ramifiedGhost π q n x :=
  fun _ _ h ↦ funext fun n ↦
    eq_of_forall_le_ramifiedGhost_eq hπ (fun k _ ↦ congrFun h k) n le_rfl

/-- If `π` maps to `0` in a nontrivial `O`-algebra, the ghost map is not injective: the
sequences `(0, 0, 0, …)` and `(0, 1, 0, …)` have the same ghost components. -/
theorem not_injective_ramifiedGhost_of_algebraMap_eq_zero [Nontrivial A]
    (hπ : algebraMap O A π = 0) :
    ¬ Function.Injective fun (x : ℕ → A) n ↦ ramifiedGhost π q n x := fun h ↦ by
  have := congrFun (@h 0 (Pi.single 1 1) (funext fun n ↦ by
    simp [ramifiedGhost_of_algebraMap_eq_zero hπ])) 1
  simp at this

/-- If `π ∣ q` and `x_i ≡ y_i` modulo `π` for every `i ≤ n`, then `w_n(x) ≡ w_n(y)` modulo
`π ^ (n + 1)`. -/
theorem pow_succ_dvd_ramifiedGhost_sub_ramifiedGhost (hq : algebraMap O A π ∣ (q : A)) {n : ℕ}
    {x y : ℕ → A} (h : ∀ i ≤ n, algebraMap O A π ∣ x i - y i) :
    algebraMap O A π ^ (n + 1) ∣ ramifiedGhost π q n x - ramifiedGhost π q n y := by
  rw [ramifiedGhost_def, ramifiedGhost_def, ← sum_sub_distrib]
  refine dvd_sum fun i hi ↦ ?_
  have hi : i ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hi)
  rw [← mul_sub, show n + 1 = i + (n - i + 1) by omega, pow_add]
  exact mul_dvd_mul_left _ (pow_succ_dvd_pow_pow_sub_pow_pow hq (h i hi) _)

/-- If `π ∣ q` and `σ` lifts `a ↦ a ^ q` modulo `π`, then every sequence of ghost components
satisfies Dwork's congruence `w_{n+1}(x) ≡ σ (w_n(x))` modulo `π ^ (n + 1)`. -/
theorem pow_succ_dvd_ramifiedGhost_succ_sub (hq : algebraMap O A π ∣ (q : A)) (σ : A →ₐ[O] A)
    (hσ : ∀ a, algebraMap O A π ∣ σ a - a ^ q) (n : ℕ) (x : ℕ → A) :
    algebraMap O A π ^ (n + 1) ∣ ramifiedGhost π q (n + 1) x - σ (ramifiedGhost π q n x) := by
  rw [ramifiedGhost_succ, map_ramifiedGhost, add_sub_right_comm]
  exact dvd_add (pow_succ_dvd_ramifiedGhost_sub_ramifiedGhost hq fun i _ ↦
    dvd_sub_comm.1 (hσ (x i))) (dvd_mul_right _ _)

open scoped Classical in
/-- One step of the recursive construction of a ghost preimage of `y`: keep the coordinates
`x_0, …, x_n` and choose `x_{n+1}` with `π ^ (n + 1) x_{n+1} = y_{n+1} - w_n(x ^ q)`, if
possible. -/
private noncomputable def ghostPreimageStep (π : O) (q : ℕ) (y : ℕ → A) (n : ℕ) (x : ℕ → A) :
    ℕ → A :=
  Function.update x (n + 1) <|
    if h : algebraMap O A π ^ (n + 1) ∣ y (n + 1) - ramifiedGhost π q n (fun i ↦ x i ^ q) then
      h.choose
    else 0

/-- The `n`-th approximation to a ghost preimage of `y`, built from `ghostPreimageStep`. -/
private noncomputable def ghostPreimageAux (π : O) (q : ℕ) (y : ℕ → A) : ℕ → ℕ → A
  | 0 => fun _ ↦ y 0
  | n + 1 => ghostPreimageStep π q y n (ghostPreimageAux π q y n)

/-- Later approximations do not change earlier coordinates. -/
private theorem ghostPreimageAux_of_le (y : ℕ → A) {k m : ℕ} (hkm : k ≤ m) :
    ghostPreimageAux π q y m k = ghostPreimageAux π q y k k := by
  induction m, hkm using Nat.le_induction with
  | base => rfl
  | succ m hkm ih =>
    rw [ghostPreimageAux, ghostPreimageStep, Function.update_of_ne (by omega), ih]

/-- Under Dwork's congruences, the `n`-th approximation has `n`-th ghost component `y n`. -/
private theorem ramifiedGhost_ghostPreimageAux (hq : algebraMap O A π ∣ (q : A))
    (σ : A →ₐ[O] A) (hσ : ∀ a, algebraMap O A π ∣ σ a - a ^ q) {y : ℕ → A}
    (hy : ∀ n, algebraMap O A π ^ (n + 1) ∣ y (n + 1) - σ (y n)) (n : ℕ) :
    ramifiedGhost π q n (ghostPreimageAux π q y n) = y n := by
  induction n with
  | zero => simp [ghostPreimageAux]
  | succ n ih =>
    rw [ghostPreimageAux]
    set x := ghostPreimageAux π q y n
    -- `y_{n+1} - w_n(x ^ q) = (y_{n+1} - σ (y_n)) + (σ (w_n(x)) - w_n(x ^ q))` is divisible by
    -- `π ^ (n + 1)`, so the step solves `π ^ (n + 1) x_{n+1} = y_{n+1} - w_n(x ^ q)`.
    have hdvd : algebraMap O A π ^ (n + 1) ∣ y (n + 1) - ramifiedGhost π q n (fun i ↦ x i ^ q) := by
      have h := dvd_add (hy n)
        (pow_succ_dvd_ramifiedGhost_sub_ramifiedGhost hq fun i _ ↦ hσ (x i))
      rwa [← map_ramifiedGhost, ih, sub_add_sub_cancel] at h
    simp only [ghostPreimageStep, hdvd, ↓reduceDIte]
    rw [ramifiedGhost_succ, Function.update_self,
      ← hdvd.choose_spec, ramifiedGhost_congr fun i hi ↦ by
        rw [Function.update_of_ne (by omega)], add_sub_cancel]

/-- **The ramified Dwork criterion.** Suppose `π ∣ q` in `A` and `σ` is an `O`-algebra
endomorphism of `A` lifting `a ↦ a ^ q` modulo `π`. A sequence `y` is the sequence of ramified
ghost components of some `x` if and only if `y (n + 1) ≡ σ (y n)` modulo `π ^ (n + 1)` for every
`n`. Neither completeness nor `π`-torsion-freeness of `A` is needed; the latter gives uniqueness of
`x`, by `ramifiedGhost_injective`. -/
theorem exists_ramifiedGhost_eq_iff (hq : algebraMap O A π ∣ (q : A)) (σ : A →ₐ[O] A)
    (hσ : ∀ a, algebraMap O A π ∣ σ a - a ^ q) (y : ℕ → A) :
    (∃ x : ℕ → A, ∀ n, ramifiedGhost π q n x = y n) ↔
      ∀ n, algebraMap O A π ^ (n + 1) ∣ y (n + 1) - σ (y n) := by
  refine ⟨fun ⟨x, hx⟩ n ↦ ?_, fun hy ↦ ?_⟩
  · rw [← hx, ← hx]
    exact pow_succ_dvd_ramifiedGhost_succ_sub hq σ hσ n x
  · refine ⟨fun k ↦ ghostPreimageAux π q y k k, fun n ↦ ?_⟩
    rw [ramifiedGhost_congr fun i hi ↦ (ghostPreimageAux_of_le y hi).symm]
    exact ramifiedGhost_ghostPreimageAux hq σ hσ hy n

/-- The ramified Dwork criterion over a local ring `O` whose maximal ideal is contained in `(π)`
(for instance a discrete valuation ring with uniformizer `π`) and whose residue field is finite,
with `q` the cardinality of the residue field. -/
theorem exists_ramifiedGhost_natCard_residueField_eq_iff [IsLocalRing O]
    [Finite (IsLocalRing.ResidueField O)] (hπ : IsLocalRing.maximalIdeal O ≤ Ideal.span {π})
    (σ : A →ₐ[O] A)
    (hσ : ∀ a, algebraMap O A π ∣ σ a - a ^ Nat.card (IsLocalRing.ResidueField O))
    (y : ℕ → A) :
    (∃ x : ℕ → A, ∀ n, ramifiedGhost π (Nat.card (IsLocalRing.ResidueField O)) n x = y n) ↔
      ∀ n, algebraMap O A π ^ (n + 1) ∣ y (n + 1) - σ (y n) := by
  refine exists_ramifiedGhost_eq_iff ?_ σ hσ y
  -- The cardinality `q` of the residue field vanishes in it, so `q ∈ 𝔪 ≤ (π)`.
  have : Fintype (IsLocalRing.ResidueField O) := Fintype.ofFinite _
  have hmem : (Nat.card (IsLocalRing.ResidueField O) : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, Nat.card_eq_fintype_card,
      FiniteField.cast_card_eq_zero]
  simpa using map_dvd (algebraMap O A) (Ideal.mem_span_singleton.1 (hπ hmem))

end Dwork

namespace WittVector

open _root_.WittVector

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A]

/-- **Dwork's criterion** for `p`-typical Witt vectors: if `σ` is a ring endomorphism of `A`
lifting the Frobenius modulo `p`, a sequence `y` is the ghost sequence of a Witt vector if and only
if `y (n + 1) ≡ σ (y n)` modulo `p ^ (n + 1)` for every `n`. -/
theorem mem_range_ghostMap_iff (σ : A →+* A) (hσ : ∀ a, (p : A) ∣ σ a - a ^ p) (y : ℕ → A) :
    y ∈ Set.range (ghostMap : _root_.WittVector p A → ℕ → A) ↔
      ∀ n, (p : A) ^ (n + 1) ∣ y (n + 1) - σ (y n) := by
  have h := exists_ramifiedGhost_eq_iff (π := (p : ℤ)) (q := p) (by simp) σ.toIntAlgHom
    (by simpa using hσ) y
  simp only [map_natCast, RingHom.toIntAlgHom_apply] at h
  rw [← h]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.coeff, fun n ↦ by rw [ramifiedGhost_natCast_self_coeff, ghostMap_apply]⟩
  · rintro ⟨x, hx⟩
    exact ⟨mk p x, funext fun n ↦ by
      rw [ghostMap_apply, ← ramifiedGhost_natCast_self_coeff (O := ℤ), coeff_mk, hx]⟩

/-- If `p` is a nonzerodivisor of `A`, the ghost map of `p`-typical Witt vectors over `A` is
injective. -/
theorem ghostMap_injective (hp : (p : A) ∈ nonZeroDivisors A) :
    Function.Injective (ghostMap : _root_.WittVector p A → ℕ → A) := fun x y h ↦ by
  refine ext fun n ↦ congrFun (ramifiedGhost_injective (O := ℤ) (π := p) (q := p)
    (by simpa using hp) (funext fun k ↦ ?_)) n
  simpa [ramifiedGhost_natCast_self_coeff, ghostMap_apply] using congrFun h k

end WittVector

end TauCeti
