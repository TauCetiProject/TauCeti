/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.NoncrossingPartition.Catalan
public import TauCeti.Probability.FreeProbability.Cumulant.Free

/-!
# Semicircular elements

Let `φ : A →ₗ[R] R` be a linear functional on an algebra `A` over a commutative ring `R`. An
element `a : A` is *semicircular of variance `v`* for `φ` when it has the moments of the centred
semicircle law of variance `v`:

`φ (a ^ (2 * k)) = v ^ k * catalan k` and `φ (a ^ (2 * k + 1)) = 0`.

For `R = ℝ` or `ℂ` and real `v ≥ 0` these are the moments of the centred semicircle law of
variance `v`, with density `(2π v)⁻¹ √(4v - t²)` on `[-2√v, 2√v]`; at `v = 0` it is the Dirac mass
at `0`. The case `k = 0` forces `φ 1 = 1`.

The free cumulants characterize semicircular elements: `a` is semicircular of variance `v` exactly
when its second free cumulant `κ₂(a, a)` is `v` and all its other free cumulants `κ_n(a, …, a)`,
`n ≥ 1`, vanish. One direction is the moment–cumulant formula, in which only the noncrossing
pairings survive; the other is the uniqueness of the free cumulants. Since free cumulants are
additive on free elements, the sum of free semicircular elements is semicircular, with the sum of
the variances; this is the algebraic form of the identity `σ_v ⊞ σ_w = σ_(v + w)` for the free
additive convolution of semicircle laws.

No positivity or traciality of `φ` is assumed. The comparison with the law of a selfadjoint element
of a C⋆-algebra is in `TauCeti.Probability.FreeProbability.Semicircular.Law`.

## Main definitions

* `TauCeti.IsSemicircular φ a v` — `a` is semicircular of variance `v` for `φ`.

## Main results

* `TauCeti.isSemicircular_iff_apply_pow` — the moments of a semicircular element in one formula.
* `TauCeti.IsSemicircular.freeCumulant_const` — the free cumulant of `(a, …, a)` along a nonempty
  set of positions is `v` for two positions and `0` otherwise.
* `TauCeti.isSemicircular_iff_freeCumulant_const` — for a normalised `φ`, this characterizes
  semicircular elements; `TauCeti.isSemicircular_add_algebraMap_iff_freeCumulant_const` and
  `TauCeti.isSemicircular_sub_algebraMap_iff_freeCumulant_const` characterize scalar shifts by a
  centring condition and the higher free cumulants.
* `TauCeti.IsSemicircular.smul`, `TauCeti.IsSemicircular.neg`, and `TauCeti.isSemicircular_zero` —
  rescaling, negation, and the degenerate case of variance zero.
* `TauCeti.IsFreelyIndependentElements.isSemicircular_add` and
  `TauCeti.IsFreelyIndependentElements.isSemicircular_sum` — sums of free semicircular elements
  are semicircular, with the sum of the variances.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 2 for
  semicircular elements, Lecture 11 for their free cumulants, and Lecture 12 for their sums.
-/

public section

open Finset

namespace TauCeti

variable {R A ι : Type*} [CommRing R] [Semiring A] [Algebra R A] {φ : A →ₗ[R] R} {a : A}
  {v w : R}

/-- An element `a` is *semicircular of variance `v`* for the functional `φ` if it has the moments
of the centred semicircle law of variance `v`: `φ (a ^ (2 * k)) = v ^ k * catalan k` and
`φ (a ^ (2 * k + 1)) = 0`. -/
structure IsSemicircular (φ : A →ₗ[R] R) (a : A) (v : R) : Prop where
  /-- The even moments are `v ^ k * catalan k`. -/
  apply_pow_two_mul (k : ℕ) : φ (a ^ (2 * k)) = v ^ k * catalan k
  /-- The odd moments vanish. -/
  apply_pow_two_mul_add_one (k : ℕ) : φ (a ^ (2 * k + 1)) = 0

/-- An element is semicircular of variance `v` exactly when its `n`-th moment is
`v ^ (n / 2) * catalan (n / 2)` for even `n` and `0` for odd `n`. -/
theorem isSemicircular_iff_apply_pow :
    IsSemicircular φ a v ↔
      ∀ n : ℕ, φ (a ^ n) = if Even n then v ^ (n / 2) * catalan (n / 2) else 0 := by
  refine ⟨fun h n => ?_, fun h => ⟨fun k => ?_, fun k => ?_⟩⟩
  · obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · simp [h.apply_pow_two_mul]
    · simp [h.apply_pow_two_mul_add_one]
  · simp [h]
  · simp [h]

namespace IsSemicircular

/-- The moments of a semicircular element of variance `v`: the `n`-th moment is
`v ^ (n / 2) * catalan (n / 2)` for even `n` and `0` for odd `n`. -/
theorem apply_pow (h : IsSemicircular φ a v) (n : ℕ) :
    φ (a ^ n) = if Even n then v ^ (n / 2) * catalan (n / 2) else 0 :=
  isSemicircular_iff_apply_pow.1 h n

/-- A functional with a semicircular element is normalised. -/
theorem apply_one (h : IsSemicircular φ a v) : φ 1 = 1 := by
  simpa using h.apply_pow_two_mul 0

/-- A semicircular element is centred. -/
theorem apply_self (h : IsSemicircular φ a v) : φ a = 0 := by
  simpa using h.apply_pow_two_mul_add_one 0

/-- A semicircular element of variance `v` has second moment `v`. -/
theorem apply_pow_two (h : IsSemicircular φ a v) : φ (a ^ 2) = v := by
  simpa using h.apply_pow_two_mul 1

/-- The variance of a semicircular element is unique. -/
theorem unique (h : IsSemicircular φ a v) (h' : IsSemicircular φ a w) : v = w :=
  h.apply_pow_two.symm.trans h'.apply_pow_two

/-- Rescaling a semicircular element of variance `v` by `c` gives a semicircular element of
variance `c ^ 2 * v`. -/
theorem smul (h : IsSemicircular φ a v) (c : R) : IsSemicircular φ (c • a) (c ^ 2 * v) where
  apply_pow_two_mul k := by
    rw [smul_pow, map_smul, h.apply_pow_two_mul, smul_eq_mul, mul_pow, pow_mul]
    ring
  apply_pow_two_mul_add_one k := by
    rw [smul_pow, map_smul, h.apply_pow_two_mul_add_one, smul_zero]

/-- Negating a semicircular element in a ring preserves its variance. -/
theorem neg {B : Type*} [Ring B] [Algebra R B] {ψ : B →ₗ[R] R} {b : B}
    (h : IsSemicircular ψ b v) : IsSemicircular ψ (-b) v := by
  simpa using h.smul (-1 : R)

/-- *The free cumulants of a semicircular element*: the free cumulant of the constant word
`(a, …, a)` along a nonempty set `s` of positions is `v` if `s` has two elements and `0`
otherwise. Only the second free cumulant `κ₂(a, a) = v` is nonzero. -/
theorem freeCumulant_const (h : IsSemicircular φ a v) {α : Type*} [LinearOrder α]
    {s : Finset α} (hs : s.Nonempty) :
    freeCumulant φ (fun _ => a) s = if #s = 2 then v else 0 :=
  freeCumulant_const_eq_of_forall_apply_pow φ (fun n => if n = 2 then v else 0) hs
    fun t _ _ => by rw [h.apply_pow, NoncrossingPartition.sum_prod_ite_card_eq_two]

end IsSemicircular

/-- *Semicircular elements are characterized by their free cumulants*: for a normalised `φ`, an
element `a` is semicircular of variance `v` exactly when its free cumulants `κ_n(a, …, a)`,
`n ≥ 1`, are `κ₂ = v` and `κ_n = 0` for `n ≠ 2`. -/
theorem isSemicircular_iff_freeCumulant_const (hφ : φ 1 = 1) :
    IsSemicircular φ a v ↔
      ∀ n : ℕ, n ≠ 0 → freeCumulant φ (fun _ : Fin n => a) univ = if n = 2 then v else 0 := by
  refine ⟨fun h n hn => ?_, fun h => isSemicircular_iff_apply_pow.2 fun n => ?_⟩
  · have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    simpa using h.freeCumulant_const (univ_nonempty (α := Fin n))
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hφ]
  -- By the moment–cumulant formula, only the noncrossing pairings contribute to the moments.
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have hκ (B : Finset (Fin n)) (hB : B.Nonempty) :
      freeCumulant φ (fun _ => a) B = if #B = 2 then v else 0 := by
    rw [freeCumulant_eq_freeCumulant_comp_orderEmbOfFin, Function.comp_def,
      h _ hB.card_pos.ne']
  have hm := apply_pow_card_eq_sum_prod_freeCumulant φ a (univ_nonempty (α := Fin n))
  have hc := NoncrossingPartition.sum_prod_ite_card_eq_two (univ : Finset (Fin n)) v
  rw [card_univ, Fintype.card_fin] at hm hc
  rw [hm, ← hc]
  exact sum_congr rfl fun π _ =>
    prod_congr rfl fun B hB => hκ B (π.1.nonempty_of_mem_parts hB)

/-- For a normalised `φ`, `a + algebraMap R A c` is semicircular of variance `v` if and only if
`φ a + c = 0`, `κ₂(a, a) = v`, and `κ_n(a, …, a) = 0` for every `n > 2`. -/
theorem isSemicircular_add_algebraMap_iff_freeCumulant_const (hφ : φ 1 = 1) {c : R} :
    IsSemicircular φ (a + algebraMap R A c) v ↔
      φ a + c = 0 ∧ ∀ n : ℕ, 2 ≤ n →
        freeCumulant φ (fun _ : Fin n => a) univ = if n = 2 then v else 0 := by
  rw [isSemicircular_iff_freeCumulant_const hφ]
  have h1 : freeCumulant φ (fun _ : Fin 1 => a + algebraMap R A c) univ = φ a + c := by
    rw [univ_unique, freeCumulant_singleton]
    simp [Algebra.algebraMap_eq_smul_one, hφ]
  have hgt {n : ℕ} (hn : 2 ≤ n) :
      freeCumulant φ (fun _ : Fin n => a + algebraMap R A c) univ =
        freeCumulant φ (fun _ : Fin n => a) univ := by
    have hcard : 1 < #(univ : Finset (Fin n)) := by
      rw [card_univ, Fintype.card_fin]
      omega
    exact freeCumulant_add_algebraMap φ (fun _ : Fin n => a) hφ (fun _ => c) hcard
  refine ⟨fun h => ⟨h1 ▸ h 1 one_ne_zero, fun n hn => ?_⟩, fun ⟨hc, h⟩ n hn => ?_⟩
  · rw [← hgt hn]
    exact h n (by omega)
  · rcases eq_or_ne n 1 with rfl | hn1
    · rw [h1, hc]
      simp
    · rw [hgt (by omega)]
      exact h n (by omega)

/-- *Shifted semicircular elements via free cumulants*: in an `R`-algebra ring, for a normalised
`ψ`, `b - algebraMap R B m` is semicircular of variance `v` if and only if `ψ b = m`,
`κ₂(b, b) = v`, and `κ_n(b, …, b) = 0` for every `n > 2`. -/
theorem isSemicircular_sub_algebraMap_iff_freeCumulant_const {B : Type*} [Ring B] [Algebra R B]
    {ψ : B →ₗ[R] R} {b : B} (hψ : ψ 1 = 1) {m : R} :
    IsSemicircular ψ (b - algebraMap R B m) v ↔
      ψ b = m ∧ ∀ n : ℕ, 2 ≤ n →
        freeCumulant ψ (fun _ : Fin n => b) univ = if n = 2 then v else 0 := by
  rw [sub_eq_add_neg, ← map_neg, isSemicircular_add_algebraMap_iff_freeCumulant_const hψ,
    ← sub_eq_add_neg, sub_eq_zero]

/-- For a normalised `φ`, the zero element is semicircular of variance zero. -/
theorem isSemicircular_zero (hφ : φ 1 = 1) : IsSemicircular φ (0 : A) 0 where
  apply_pow_two_mul k := by
    rcases eq_or_ne k 0 with rfl | hk
    · simp [hφ]
    · simp [hk]
  apply_pow_two_mul_add_one k := by simp

namespace IsFreelyIndependentElements

variable {c : ι → A}

/-- *The sum of free semicircular elements is semicircular*: if the elements `c k` are freely
independent for a normalised `φ`, and `c k` is semicircular of variance `v k` for `k ∈ T`, then
`∑ k ∈ T, c k` is semicircular of variance `∑ k ∈ T, v k`. -/
theorem isSemicircular_sum (h : IsFreelyIndependentElements φ c) (hφ : φ 1 = 1) (T : Finset ι)
    {v : ι → R} (hc : ∀ k ∈ T, IsSemicircular φ (c k) (v k)) :
    IsSemicircular φ (∑ k ∈ T, c k) (∑ k ∈ T, v k) := by
  refine (isSemicircular_iff_freeCumulant_const hφ).2 fun n hn => ?_
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  rw [h.freeCumulant_sum hφ T univ_nonempty, sum_congr rfl fun k hk =>
    (isSemicircular_iff_freeCumulant_const hφ).1 (hc k hk) n hn]
  split_ifs <;> simp

/-- *The sum of two free semicircular elements is semicircular*: if `c i` and `c j`, for `i ≠ j`,
belong to a freely independent family and are semicircular of variances `v` and `w`, then
`c i + c j` is semicircular of variance `v + w`. -/
theorem isSemicircular_add (h : IsFreelyIndependentElements φ c) {i j : ι} (hij : i ≠ j)
    (hi : IsSemicircular φ (c i) v) (hj : IsSemicircular φ (c j) w) :
    IsSemicircular φ (c i + c j) (v + w) := by
  classical
  simpa [sum_pair hij, hij.symm] using h.isSemicircular_sum hi.apply_one {i, j}
    (v := fun k => if k = i then v else w) (by simpa [hij.symm] using ⟨hi, hj⟩)

end IsFreelyIndependentElements

end TauCeti
