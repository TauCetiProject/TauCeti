/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.NoncrossingPartition.Narayana
public import TauCeti.Probability.FreeProbability.Semicircular.Basic

/-!
# Free Poisson elements

Let `φ : A →ₗ[R] R` be a linear functional on an algebra `A` over a commutative ring `R`. An
element `a : A` is *free Poisson of rate `r` and jump size `c`* for `φ` when it has the moments

`φ (a ^ n) = c ^ n * ∑_{π ∈ NC(n)} r ^ |π|`,

where `|π|` is the number of parts of the noncrossing partition `π`. By the moment–cumulant formula
these are exactly the moments of an element whose free cumulants are `κ_n(a, …, a) = r * c ^ n` for
every `n ≥ 1`: each part `B` of `π` contributes `r * c ^ |B|`, and the sizes of the parts add up to
`n`. For real `r ≥ 0` and `c` these are the moments of the free Poisson law (Marchenko–Pastur law)
of rate `r` and jump size `c`; for `c = 1` the polynomial `∑_{π ∈ NC(n)} r ^ |π|` is the Narayana
polynomial of `n`. The case `n = 0` forces `φ 1 = 1`.

The free cumulants characterize free Poisson elements, which makes their algebra transparent:
rescaling by `d` multiplies the jump size by `d`, the zero element is free Poisson exactly when
`r * c = 0`, and since free cumulants are additive on free elements, a sum of free elements that are
free Poisson with a common jump size `c` is free Poisson of jump size `c`, with the sum of the
rates. This is the algebraic form of the identity `π_{r, c} ⊞ π_{r', c} = π_{r + r', c}` for the
free additive convolution of free Poisson laws. The square of a semicircular element of variance
`v` is free Poisson of rate `1` and jump size `v`, since both have the moments `v ^ n * catalan n`.

No positivity or traciality of `φ` is assumed. The free Poisson limit theorem, which realizes these
moments as limits of sums of many free elements with small Bernoulli moments, is in
`TauCeti.Probability.FreeProbability.PoissonLimit`.

## Main definitions

* `TauCeti.IsFreePoisson φ a r c` — `a` is free Poisson of rate `r` and jump size `c` for `φ`.

## Main results

* `TauCeti.IsFreePoisson.freeCumulant_const` — the free cumulant of `(a, …, a)` along a nonempty
  set `s` of positions is `r * c ^ #s`.
* `TauCeti.isFreePoisson_iff_freeCumulant_const` — for a normalised `φ`, this characterizes free
  Poisson elements.
* `TauCeti.IsFreePoisson.smul` and `TauCeti.isFreePoisson_zero_iff` — rescaling, and the degenerate
  laws.
* `TauCeti.IsFreelyIndependentElements.isFreePoisson_add` and
  `TauCeti.IsFreelyIndependentElements.isFreePoisson_sum` — sums of free free Poisson elements with
  a common jump size are free Poisson, with the sum of the rates.
* `TauCeti.IsSemicircular.isFreePoisson_sq` — the square of a semicircular element of variance `v`
  is free Poisson of rate `1` and jump size `v`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 12 for free
  Poisson elements and their free cumulants.
-/

public section

open Finset

namespace TauCeti

variable {R A ι : Type*} [CommRing R] [Semiring A] [Algebra R A] {φ : A →ₗ[R] R} {a : A}
  {r c : R}

/-- An element `a` is *free Poisson of rate `r` and jump size `c`* for the functional `φ` if it
has the moments of the free Poisson law of rate `r` and jump size `c`:
`φ (a ^ n) = c ^ n * ∑_{π ∈ NC(n)} r ^ |π|`, where `|π|` is the number of parts of `π`. -/
structure IsFreePoisson (φ : A →ₗ[R] R) (a : A) (r c : R) : Prop where
  /-- The `n`-th moment is `c ^ n * ∑_{π ∈ NC(n)} r ^ |π|`. -/
  apply_pow (n : ℕ) :
    φ (a ^ n) = c ^ n * ∑ π : NoncrossingPartition (univ : Finset (Fin n)), r ^ #π.1.parts

/-- An element is free Poisson of rate `r` and jump size `c` exactly when it has the moments
`φ (a ^ n) = c ^ n * ∑_{π ∈ NC(n)} r ^ |π|`. -/
theorem isFreePoisson_iff_apply_pow :
    IsFreePoisson φ a r c ↔ ∀ n : ℕ,
      φ (a ^ n) = c ^ n * ∑ π : NoncrossingPartition (univ : Finset (Fin n)), r ^ #π.1.parts :=
  ⟨fun h => h.apply_pow, fun h => ⟨h⟩⟩

namespace IsFreePoisson

/-- A functional with a free Poisson element is normalised. -/
theorem apply_one (h : IsFreePoisson φ a r c) : φ 1 = 1 := by
  have h0 := h.apply_pow 0
  rwa [pow_zero, pow_zero, NoncrossingPartition.sum_comp_card_parts_of_card_eq_zero (by simp)
    fun k => r ^ k, pow_zero, one_mul] at h0

/-- *The free cumulants of a free Poisson element*: the free cumulant of the constant word
`(a, …, a)` along a nonempty set `s` of positions is `r * c ^ #s`. -/
theorem freeCumulant_const (h : IsFreePoisson φ a r c) {α : Type*} [LinearOrder α]
    {s : Finset α} (hs : s.Nonempty) :
    freeCumulant φ (fun _ => a) s = r * c ^ #s :=
  freeCumulant_const_eq_of_forall_apply_pow φ (fun n => r * c ^ n) hs
    fun t _ _ => by rw [h.apply_pow, NoncrossingPartition.sum_prod_mul_pow_card]

/-- A free Poisson element of rate `r` and jump size `c` has mean `r * c`. -/
theorem apply_self (h : IsFreePoisson φ a r c) : φ a = r * c := by
  simpa using h.freeCumulant_const (singleton_nonempty 0)

/-- A free Poisson element of rate `r` and jump size `c` has second moment
`r * c ^ 2 + (r * c) ^ 2`, so its variance `κ₂(a, a)` is `r * c ^ 2`. -/
theorem apply_pow_two (h : IsFreePoisson φ a r c) : φ (a ^ 2) = r * c ^ 2 + (r * c) ^ 2 := by
  have := h.freeCumulant_const (insert_nonempty 0 {1})
  rw [freeCumulant_pair φ _ zero_lt_one, h.apply_self, card_pair zero_ne_one] at this
  rw [sq a, ← this]
  ring

/-- Rescaling a free Poisson element of rate `r` and jump size `c` by `d` gives a free Poisson
element of rate `r` and jump size `d * c`. -/
theorem smul (h : IsFreePoisson φ a r c) (d : R) : IsFreePoisson φ (d • a) r (d * c) where
  apply_pow n := by rw [smul_pow, map_smul, h.apply_pow, smul_eq_mul, mul_pow, mul_assoc]

end IsFreePoisson

/-- *Free Poisson elements are characterized by their free cumulants*: for a normalised `φ`, an
element `a` is free Poisson of rate `r` and jump size `c` exactly when its free cumulants are
`κ_n(a, …, a) = r * c ^ n` for every `n ≥ 1`. -/
theorem isFreePoisson_iff_freeCumulant_const (hφ : φ 1 = 1) :
    IsFreePoisson φ a r c ↔
      ∀ n : ℕ, n ≠ 0 → freeCumulant φ (fun _ : Fin n => a) univ = r * c ^ n := by
  refine ⟨fun h n hn => ?_, fun h => ⟨fun n => ?_⟩⟩
  · have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    simpa using h.freeCumulant_const (univ_nonempty (α := Fin n))
  rcases eq_or_ne n 0 with rfl | hn
  · rw [pow_zero, hφ, NoncrossingPartition.sum_comp_card_parts_of_card_eq_zero (by simp)
      fun k => r ^ k, pow_zero, pow_zero, one_mul]
  -- By the moment–cumulant formula, each part `B` contributes the cumulant `r * c ^ #B`.
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have hκ (B : Finset (Fin n)) (hB : B.Nonempty) :
      freeCumulant φ (fun _ => a) B = r * c ^ #B := by
    rw [freeCumulant_eq_freeCumulant_comp_orderEmbOfFin, Function.comp_def,
      h _ hB.card_pos.ne']
  have hm := apply_pow_card_eq_sum_prod_freeCumulant φ a (univ_nonempty (α := Fin n))
  have hc := NoncrossingPartition.sum_prod_mul_pow_card (univ : Finset (Fin n)) r c
  rw [card_univ, Fintype.card_fin] at hm hc
  rw [hm, ← hc]
  exact sum_congr rfl fun π _ =>
    prod_congr rfl fun B hB => hκ B (π.1.nonempty_of_mem_parts hB)

/-- For a normalised `φ`, the zero element is free Poisson of rate `r` and jump size `c` exactly
when `r * c = 0`: its moments are those of the Dirac mass at `0`, which is the free Poisson law
whenever the rate or the jump size vanishes. -/
theorem isFreePoisson_zero_iff (hφ : φ 1 = 1) : IsFreePoisson φ (0 : A) r c ↔ r * c = 0 := by
  refine ⟨fun h => by simpa using h.apply_self.symm, fun hrc => ?_⟩
  refine (isFreePoisson_iff_freeCumulant_const hφ).2 fun n hn => ?_
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  rw [pow_succ, ← mul_assoc, mul_right_comm, hrc, zero_mul, ← freeCumulantMultilinear_apply]
  exact (freeCumulantMultilinear φ).map_zero

namespace IsFreelyIndependentElements

variable {x : ι → A}

/-- *The sum of free free Poisson elements is free Poisson*: if the elements `x k` are freely
independent for a normalised `φ`, and `x k` is free Poisson of rate `r k` and jump size `c` for
`k ∈ T`, then `∑ k ∈ T, x k` is free Poisson of rate `∑ k ∈ T, r k` and jump size `c`. -/
theorem isFreePoisson_sum (h : IsFreelyIndependentElements φ x) (hφ : φ 1 = 1) (T : Finset ι)
    {r : ι → R} (hx : ∀ k ∈ T, IsFreePoisson φ (x k) (r k) c) :
    IsFreePoisson φ (∑ k ∈ T, x k) (∑ k ∈ T, r k) c := by
  refine (isFreePoisson_iff_freeCumulant_const hφ).2 fun n hn => ?_
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  rw [h.freeCumulant_sum hφ T univ_nonempty, sum_congr rfl fun k hk =>
    (isFreePoisson_iff_freeCumulant_const hφ).1 (hx k hk) n hn, sum_mul]

/-- *The sum of two free free Poisson elements is free Poisson*: if `x i` and `x j`, for `i ≠ j`,
belong to a freely independent family and are free Poisson of rates `r` and `r'` with a common jump
size `c`, then `x i + x j` is free Poisson of rate `r + r'` and jump size `c`. -/
theorem isFreePoisson_add (h : IsFreelyIndependentElements φ x) {i j : ι} (hij : i ≠ j)
    {r' : R} (hi : IsFreePoisson φ (x i) r c) (hj : IsFreePoisson φ (x j) r' c) :
    IsFreePoisson φ (x i + x j) (r + r') c := by
  classical
  simpa [sum_pair hij, hij.symm] using h.isFreePoisson_sum hi.apply_one {i, j}
    (r := fun k => if k = i then r else r') (by simpa [hij.symm] using ⟨hi, hj⟩)

end IsFreelyIndependentElements

/-- *The square of a semicircular element is free Poisson*: if `a` is semicircular of variance
`v`, then `a ^ 2` is free Poisson of rate `1` and jump size `v`. Both have the moments
`v ^ n * catalan n`. -/
theorem IsSemicircular.isFreePoisson_sq {v : R} (h : IsSemicircular φ a v) :
    IsFreePoisson φ (a ^ 2) 1 v where
  apply_pow n := by
    simp [← pow_mul, h.apply_pow_two_mul, NoncrossingPartition.card_fin_eq_catalan]

end TauCeti
