/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.IncidenceAlgebra
public import TauCeti.Combinatorics.NoncrossingPartition.Basic
public import TauCeti.Data.Finset.Sort

/-!
# Free cumulants

Let `φ : A → R` be a function on a monoid `A` (in free probability, a linear functional on an
algebra `A`, used through its coercion to a function), and let `a : α → A` assign an element of
`A` to each position of a linear order `α`. For a finite set `s` of positions and a finite
partition `P` of `s`, the *block moment* `φ_P(a)` is the product over the parts `B` of `P` of the
moments `φ (a_{b₁} * ⋯ * a_{bₖ})`, where `b₁ < ⋯ < bₖ` lists `B` in increasing order.

The *free cumulants* are obtained from the block moments by Möbius inversion on the lattice
`NC(s)` of noncrossing partitions of `s`: for `π ∈ NC(s)`,
`κ_π(a) = ∑_{σ ≤ π} μ(σ, π) φ_σ(a)`, where `μ` is the Möbius function of `NC(s)`, and the free
cumulant of the word `(a_i)_{i ∈ s}` is `κ_s(a) = κ_{1_s}(a)` for the partition `1_s` of `s` into
one part. Equivalently, the cumulants are the unique family satisfying the moment–cumulant formula
`φ_π(a) = ∑_{σ ≤ π} κ_σ(a)`; in particular, for nonempty `s`,
`φ (a_{i₁} * ⋯ * a_{iₙ}) = ∑_{π ∈ NC(s)} κ_π(a)` where `i₁ < ⋯ < iₙ` lists `s`. Taking
`s = Finset.univ : Finset (Fin n)` gives the cumulants `κ_n(a₁, …, aₙ)` of free probability.

No normalisation `φ 1 = 1`, positivity or traciality is assumed. For `s = ∅` the cumulant
`κ_∅(a)` is the empty product `1`; it carries no meaning, since free cumulants are indexed by
`n ≥ 1`.

## Main definitions

* `TauCeti.partitionMoment φ a P` — the block moment `φ_P(a)` of a finite partition `P`.
* `TauCeti.partitionCumulant φ a π` — the free cumulant `κ_π(a)` of a noncrossing partition `π`,
  defined by Möbius inversion on `NC(s)`.
* `TauCeti.freeCumulant φ a s` — the free cumulant `κ_s(a)` of the word `(a_i)_{i ∈ s}`.

## Main results

* `TauCeti.sum_Iic_partitionCumulant` — the moment–cumulant formula
  `∑_{σ ≤ π} κ_σ(a) = φ_π(a)`, and `TauCeti.eq_partitionCumulant_of_forall_sum_Iic` — the
  cumulants are the only family satisfying it.
* `TauCeti.apply_prod_eq_sum_partitionCumulant` and
  `TauCeti.apply_prod_ofFn_eq_sum_partitionCumulant` — a moment is the sum of the cumulants over
  all noncrossing partitions.
* `TauCeti.freeCumulant_eq_sum_mu_mul_partitionMoment` — the cumulant is the sum of the block
  moments weighted by `μ(π, 1_s)`.
* `TauCeti.freeCumulant_singleton` and `TauCeti.freeCumulant_pair` — the first two cumulants are
  the mean `φ a_i` and the covariance `φ (a_i * a_j) - φ a_i * φ a_j`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 10 and 11.
* R. Speicher, *Multiplicative functions on the lattice of non-crossing partitions and free
  convolution*, Math. Ann. 298 (1994), 611–628.
-/

public section

open Finset IncidenceAlgebra

namespace TauCeti

variable {R A α : Type*} [LinearOrder α] {s : Finset α}

section Moment

variable [CommMonoid R] [Monoid A]

/-- The *block moment* `φ_P(a)` of a finite partition `P` of a set `s` of positions: the product
over the parts `B` of `P` of `φ (a_{b₁} * ⋯ * a_{bₖ})`, where `b₁ < ⋯ < bₖ` lists `B` in
increasing order. -/
def partitionMoment (φ : A → R) (a : α → A) (P : Finpartition s) : R :=
  ∏ B ∈ P.parts, φ ((B.sort.map a).prod)

/-- Unfolding of the block moment. -/
theorem partitionMoment_def (φ : A → R) (a : α → A) (P : Finpartition s) :
    partitionMoment φ a P = ∏ B ∈ P.parts, φ ((B.sort.map a).prod) := by
  rw [partitionMoment]

/-- The block moment of the partition into singletons is the product of the individual
moments. -/
@[simp]
theorem partitionMoment_bot (φ : A → R) (a : α → A) :
    partitionMoment φ a (⊥ : Finpartition s) = ∏ i ∈ s, φ (a i) := by
  simp [partitionMoment_def]

/-- The block moment of the partition of a nonempty set into one part is the moment of the whole
word, read in increasing order. -/
@[simp]
theorem partitionMoment_top (φ : A → R) (a : α → A) (hs : s.Nonempty) :
    partitionMoment φ a (⊤ : Finpartition s) = φ ((s.sort.map a).prod) := by
  rw [partitionMoment_def, Finpartition.parts_top hs.ne_empty, prod_singleton]

end Moment

section Cumulant

variable [CommRing R] [Monoid A]

/-- The *free cumulant* `κ_π(a)` of a noncrossing partition `π` of `s`, defined by Möbius
inversion of the block moments on the lattice of noncrossing partitions:
`κ_π(a) = ∑_{σ ≤ π} μ(σ, π) φ_σ(a)`. -/
def partitionCumulant (φ : A → R) (a : α → A) (π : NoncrossingPartition s) : R :=
  ∑ σ ∈ Iic π, mu R σ π * partitionMoment φ a σ.1

/-- Unfolding of the free cumulant of a noncrossing partition. -/
theorem partitionCumulant_def (φ : A → R) (a : α → A) (π : NoncrossingPartition s) :
    partitionCumulant φ a π = ∑ σ ∈ Iic π, mu R σ π * partitionMoment φ a σ.1 := by
  rw [partitionCumulant]

/-- The *free cumulant* `κ_s(a)` of the word `(a_i)_{i ∈ s}`: the cumulant of the partition of
`s` into one part. For `s = Finset.univ : Finset (Fin n)` with `n ≥ 1` this is the `n`-th free
cumulant `κ_n(a₁, …, aₙ)`; for `s = ∅` it is the meaningless value `1`. -/
def freeCumulant (φ : A → R) (a : α → A) (s : Finset α) : R :=
  partitionCumulant φ a (⊤ : NoncrossingPartition s)

/-- Unfolding of the free cumulant of a word. -/
theorem freeCumulant_def (φ : A → R) (a : α → A) (s : Finset α) :
    freeCumulant φ a s = partitionCumulant φ a (⊤ : NoncrossingPartition s) := by
  rw [freeCumulant]

variable (φ : A → R) (a : α → A)

/-- The *moment–cumulant formula*: the block moment of a noncrossing partition `π` is the sum of
the free cumulants of the noncrossing partitions refining `π`. -/
theorem sum_Iic_partitionCumulant (π : NoncrossingPartition s) :
    ∑ σ ∈ Iic π, partitionCumulant φ a σ = partitionMoment φ a π.1 := by
  simp_rw [partitionCumulant_def]
  exact sum_Iic_sum_Iic_mu_mul (fun σ : NoncrossingPartition s => partitionMoment φ a σ.1) π

/-- The free cumulants are the only family satisfying the moment–cumulant formula
`∑_{σ ≤ π} c_σ = φ_π(a)`. -/
theorem eq_partitionCumulant_of_forall_sum_Iic (c : NoncrossingPartition s → R)
    (hc : ∀ π, ∑ σ ∈ Iic π, c σ = partitionMoment φ a π.1) : c = partitionCumulant φ a := by
  funext π
  rw [moebius_inversion_bot c (fun σ => partitionMoment φ a σ.1) (fun σ => (hc σ).symm) π,
    partitionCumulant_def]

/-- The free cumulant of the partition into singletons is the product of the individual
moments. -/
@[simp]
theorem partitionCumulant_bot :
    partitionCumulant φ a (⊥ : NoncrossingPartition s) = ∏ i ∈ s, φ (a i) := by
  simp [partitionCumulant_def]

/-- The free cumulant of a word is the sum over the noncrossing partitions `π` of its block
moments weighted by the Möbius function, `κ_s(a) = ∑_{π ∈ NC(s)} μ(π, 1_s) φ_π(a)`. -/
theorem freeCumulant_eq_sum_mu_mul_partitionMoment (s : Finset α) :
    freeCumulant φ a s =
      ∑ π : NoncrossingPartition s, mu R π ⊤ * partitionMoment φ a π.1 := by
  rw [freeCumulant_def, partitionCumulant_def, Iic_top]

/-- The *moment–cumulant formula* for a word: a moment of a nonempty word is the sum of its free
cumulants over all noncrossing partitions, `φ (a_{i₁} * ⋯ * a_{iₙ}) = ∑_{π ∈ NC(s)} κ_π(a)` for
`s = {i₁ < ⋯ < iₙ}`. -/
theorem apply_prod_eq_sum_partitionCumulant (hs : s.Nonempty) :
    φ ((s.sort.map a).prod) = ∑ π : NoncrossingPartition s, partitionCumulant φ a π := by
  rw [← partitionMoment_top φ a hs, ← NoncrossingPartition.coe_top, ← Iic_top,
    sum_Iic_partitionCumulant]

/-- The moment–cumulant formula for a word `a₁, …, aₙ` with `n ≥ 1`:
`φ (a₁ * ⋯ * aₙ) = ∑_{π ∈ NC(n)} κ_π(a₁, …, aₙ)`. -/
theorem apply_prod_ofFn_eq_sum_partitionCumulant {n : ℕ} (hn : n ≠ 0) (a : Fin n → A) :
    φ (List.ofFn a).prod =
      ∑ π : NoncrossingPartition (univ : Finset (Fin n)), partitionCumulant φ a π := by
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  rw [← apply_prod_eq_sum_partitionCumulant φ a univ_nonempty, Fin.sort_univ, List.ofFn_eq_map]

/-- The free cumulant of the empty word is the empty product `1`. -/
@[simp]
theorem freeCumulant_empty : freeCumulant φ a ∅ = 1 := by
  rw [freeCumulant_def, Subsingleton.elim (⊤ : NoncrossingPartition (∅ : Finset α)) ⊥,
    partitionCumulant_bot, prod_empty]

/-- The first free cumulant is the mean, `κ₁(a_i) = φ a_i`. -/
@[simp]
theorem freeCumulant_singleton (i : α) : freeCumulant φ a {i} = φ (a i) := by
  rw [freeCumulant_def, Subsingleton.elim (⊤ : NoncrossingPartition ({i} : Finset α)) ⊥,
    partitionCumulant_bot, prod_singleton]

/-- The second free cumulant is the covariance, `κ₂(a_i, a_j) = φ (a_i * a_j) - φ a_i * φ a_j`
for positions `i < j`. -/
theorem freeCumulant_pair {i j : α} (hij : i < j) :
    freeCumulant φ a {i, j} = φ (a i * a j) - φ (a i) * φ (a j) := by
  have := apply_prod_eq_sum_partitionCumulant φ a (insert_nonempty i {j})
  rw [NoncrossingPartition.univ_eq_bot_top_of_pair, sum_pair
      (NoncrossingPartition.bot_ne_top_of_one_lt_card (by rw [card_pair hij.ne]; omega)),
    partitionCumulant_bot, prod_pair hij.ne, sort_pair _ hij.le hij.ne] at this
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
  rw [freeCumulant_def, this, add_sub_cancel_left]

end Cumulant

end TauCeti
