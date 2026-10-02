/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# Reading the `ℤ/2`-grading: base cases, exterior bases, and ordered products

An induction over the `ℤ/2`-grading of a Clifford algebra — Mathlib's
`CliffordAlgebra.evenOdd_induction` — hands its base case back as membership in a power of
`LinearMap.range (ι Q)` whose exponent is a `ZMod.val`. Since `(0 : ZMod 2).val` is `0` and
`(1 : ZMod 2).val` is `1`, that membership says "a scalar" in the even case and "a vector" in the
odd one. Reading it that way is bookkeeping that every such induction repeats, so it is recorded
here once and shared.

In the other direction, the ordered product `(l.map (ι Q)).prod` of a list of vectors — the
spelling `TauCeti/LinearAlgebra/CliffordAlgebra/VolumeElement.lean` uses for the volume element —
is homogeneous of degree `l.length`, which is Mathlib's
`SetLike.list_prod_map_mem_graded` for the graded monoid `CliffordAlgebra.evenOdd Q` with the
degree of each factor read off `CliffordAlgebra.ι_mem_evenOdd_one`. Reading it off by the parity of
the length is what matters downstream.

The coordinate basis of an exterior algebra is homogeneous for this grading: the basis vector
indexed by `s` has degree `s.card`, and — over a nontrivial ring, where a basis vector is nonzero
and the two graded pieces meet only in `0` — that degree is the *only* one it has. This statement
belongs to the grading API independently of any spin representation.

The grading also cuts the centre in two. Multiplying by a generator `ι Q m` shifts the degree by
one, so the two halves of the equation `x * ι Q m = ι Q m * x` live in the two different graded
pieces, and the pieces meet only in `0` (`CliffordAlgebra.evenOdd_isCompl`). Each graded part of a
central element is therefore central on the generators, hence central
(`CliffordAlgebra.mem_center_of_mem_evenOdd_of_add_mem_center`). This is what lets a description of
the centre be assembled one parity at a time, and it needs no field, no finiteness and not even
`2` invertible.

## Main results

* `CliffordAlgebra.exists_algebraMap_of_mem_range_ι_pow_zero`: in the even base case the
  element is a scalar.
* `CliffordAlgebra.exists_ι_of_mem_range_ι_pow_one`: in the odd base case it is a vector.
* `CliffordAlgebra.ι_range_pow_le_evenOdd`: the `n`-th power of the range of `ι` lies in the
  graded piece of degree `n`.
* `CliffordAlgebra.prod_map_ι_mem_evenOdd`: an ordered product of `n` generators is homogeneous
  of degree `n`, and `CliffordAlgebra.prod_map_ι_mem_evenOdd_zero_of_even_length` and
  `CliffordAlgebra.prod_map_ι_mem_evenOdd_one_of_odd_length` read that off in the even and the odd
  case.
* `Module.Basis.exteriorAlgebra_mem_evenOdd_card`: an exterior coordinate-basis vector is
  homogeneous of degree given by the cardinality of its index set, and
  `Module.Basis.exteriorAlgebra_mem_evenOdd_iff` says that this is the only degree it has.
* `CliffordAlgebra.mem_center_of_mem_evenOdd_of_add_mem_center`: the even and odd parts of a
  central element are themselves central.
-/

public section


universe u v w

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-- An element of the `(0 : ZMod 2).val`-th power of the range of `ι` is a scalar. This is the
`i = 0` half of the `range_ι_pow` hypothesis of `CliffordAlgebra.evenOdd_induction`. -/
theorem exists_algebraMap_of_mem_range_ι_pow_zero {v : CliffordAlgebra Q}
    (hv : v ∈ LinearMap.range (ι Q) ^ (0 : ZMod 2).val) :
    ∃ r : R, algebraMap R (CliffordAlgebra Q) r = v :=
  Submodule.mem_one.mp (by simpa using hv)

/-- An element of the `(1 : ZMod 2).val`-th power of the range of `ι` is a vector. This is the
`i = 1` half of the `range_ι_pow` hypothesis of `CliffordAlgebra.evenOdd_induction`. -/
theorem exists_ι_of_mem_range_ι_pow_one {v : CliffordAlgebra Q}
    (hv : v ∈ LinearMap.range (ι Q) ^ (1 : ZMod 2).val) : ∃ a, ι Q a = v := by
  simpa [ZMod.val_one] using hv

/-- **The `n`-th power of the vectors is homogeneous of degree `n`** for the `ℤ/2` grading: it is
one of the summands defining `CliffordAlgebra.evenOdd Q n`. -/
theorem ι_range_pow_le_evenOdd (n : ℕ) :
    LinearMap.range (ι Q) ^ n ≤ evenOdd Q (n : ZMod 2) := by
  rw [evenOdd]
  exact le_iSup (fun j : {m : ℕ // (m : ZMod 2) = (n : ZMod 2)} => LinearMap.range (ι Q) ^ (j : ℕ))
    ⟨n, rfl⟩

/-- **An ordered product of `n` generators is homogeneous of degree `n`** for the `ℤ/2` grading. -/
theorem prod_map_ι_mem_evenOdd (l : List M) :
    (l.map (ι Q)).prod ∈ evenOdd Q (l.length : ZMod 2) := by
  simpa using SetLike.list_prod_map_mem_graded (A := evenOdd Q) l (fun _ => (1 : ZMod 2)) (ι Q)
    fun j _ => ι_mem_evenOdd_one Q j

/-- **The ordered product of an even number of vectors is even.** -/
theorem prod_map_ι_mem_evenOdd_zero_of_even_length {l : List M} (hlen : Even l.length) :
    (l.map (ι Q)).prod ∈ evenOdd Q 0 := by
  have h : (l.length : ZMod 2) = 0 := by
    rw [← ZMod.natCast_mod l.length 2, Nat.even_iff.mp hlen, Nat.cast_zero]
  exact h ▸ prod_map_ι_mem_evenOdd l

/-- **The ordered product of an odd number of vectors is odd.** -/
theorem prod_map_ι_mem_evenOdd_one_of_odd_length {l : List M} (hlen : Odd l.length) :
    (l.map (ι Q)).prod ∈ evenOdd Q 1 := by
  have h : (l.length : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod l.length 2, Nat.odd_iff.mp hlen, Nat.cast_one]
  exact h ▸ prod_map_ι_mem_evenOdd l

/-- **A generator commutes with each graded part of a central element.** The commutator of a
generator with the even part is odd and the commutator with the odd part is even, while the two sum
to zero, so both vanish. -/
private theorem commute_ι_of_mem_evenOdd_of_add_mem_center {x₀ x₁ : CliffordAlgebra Q}
    (h₀ : x₀ ∈ evenOdd Q 0) (h₁ : x₁ ∈ evenOdd Q 1)
    (hx : x₀ + x₁ ∈ Subalgebra.center R (CliffordAlgebra Q)) (m : M) :
    Commute x₀ (ι Q m) ∧ Commute x₁ (ι Q m) := by
  have hmι : ι Q m ∈ evenOdd Q 1 := ι_mem_evenOdd_one Q m
  -- The two commutators, one odd and one even.
  have hd₀ : x₀ * ι Q m - ι Q m * x₀ ∈ evenOdd Q 1 := by
    refine Submodule.sub_mem _ ?_ ?_
    · simpa using SetLike.mul_mem_graded h₀ hmι
    · simpa using SetLike.mul_mem_graded hmι h₀
  have hd₁ : x₁ * ι Q m - ι Q m * x₁ ∈ evenOdd Q 0 := by
    refine Submodule.sub_mem _ ?_ ?_
    · have h := SetLike.mul_mem_graded h₁ hmι
      rwa [CharTwo.add_self_eq_zero] at h
    · have h := SetLike.mul_mem_graded hmι h₁
      rwa [CharTwo.add_self_eq_zero] at h
  -- Centrality makes them negatives of one another, so each lies in both graded pieces.
  have hsum : (x₀ * ι Q m - ι Q m * x₀) + (x₁ * ι Q m - ι Q m * x₁) = 0 := by
    have h := Subalgebra.mem_center_iff.mp hx (ι Q m)
    rw [mul_add, add_mul] at h
    rw [sub_add_sub_comm, h, sub_self]
  have hzero : x₀ * ι Q m - ι Q m * x₀ = 0 := by
    have hboth : x₀ * ι Q m - ι Q m * x₀ ∈ evenOdd Q 0 ⊓ evenOdd Q 1 :=
      ⟨by rw [eq_neg_of_add_eq_zero_left hsum]; exact Submodule.neg_mem _ hd₁, hd₀⟩
    rwa [(evenOdd_isCompl (Q := Q)).inf_eq_bot, Submodule.mem_bot] at hboth
  rw [hzero, zero_add, sub_eq_zero] at hsum
  exact ⟨sub_eq_zero.mp hzero, hsum⟩

/-- **The even and odd parts of a central element are central.** The `ℤ/2`-grading of a Clifford
algebra therefore induces a grading of its centre.

Nothing beyond the grading is used: no field, no finiteness, and no invertibility of `2`. -/
theorem mem_center_of_mem_evenOdd_of_add_mem_center {x₀ x₁ : CliffordAlgebra Q}
    (h₀ : x₀ ∈ evenOdd Q 0) (h₁ : x₁ ∈ evenOdd Q 1)
    (hx : x₀ + x₁ ∈ Subalgebra.center R (CliffordAlgebra Q)) :
    x₀ ∈ Subalgebra.center R (CliffordAlgebra Q) ∧
      x₁ ∈ Subalgebra.center R (CliffordAlgebra Q) := by
  have key := commute_ι_of_mem_evenOdd_of_add_mem_center h₀ h₁ hx
  constructor
  · rw [Subalgebra.mem_center_iff]
    intro y
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (s := Set.range (ι Q))
      ((adjoin_range_ι (Q := Q)).ge Algebra.mem_top)
      (by rintro _ ⟨m, rfl⟩; exact (key m).1)).symm.eq
  · rw [Subalgebra.mem_center_iff]
    intro y
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (s := Set.range (ι Q))
      ((adjoin_range_ι (Q := Q)).ge Algebra.mem_top)
      (by rintro _ ⟨m, rfl⟩; exact (key m).2)).symm.eq

end CliffordAlgebra

namespace Module.Basis

variable {R : Type u} {M : Type v} {I : Type w} [CommRing R] [AddCommGroup M] [Module R M]
  [LinearOrder I]

/-- **An exterior coordinate-basis vector is homogeneous of degree its number of coordinates.** -/
@[simp] theorem exteriorAlgebra_mem_evenOdd_card (b : Module.Basis I R M) (s : Finset I) :
    b.ExteriorAlgebra s ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm R M) (s.card : ZMod 2) := by
  rw [CliffordAlgebra.evenOdd]
  refine Submodule.mem_iSup_of_mem ⟨s.card, rfl⟩ ?_
  have h := (b.exteriorPower s.card
    (⟨s, rfl⟩ : Set.powersetCard I s.card)).2
  rw [← ExteriorAlgebra.basis_eq_coe_basis] at h
  exact h

/-- **An exterior coordinate-basis vector is homogeneous of exactly one degree**: it lies in the
graded piece `i` precisely when `i` is the parity of its number of coordinates. -/
@[simp]
theorem exteriorAlgebra_mem_evenOdd_iff [Nontrivial R] (b : Module.Basis I R M) (s : Finset I)
    (i : ZMod 2) :
    b.ExteriorAlgebra s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) i ↔
      (s.card : ZMod 2) = i := by
  refine ⟨fun hmem => ?_, fun h => h ▸ b.exteriorAlgebra_mem_evenOdd_card s⟩
  by_contra hne
  have hcard := b.exteriorAlgebra_mem_evenOdd_card s
  have hpair : ∀ c d : ZMod 2, c ≠ d → (c = 0 ∧ d = 1) ∨ (c = 1 ∧ d = 0) := by decide
  have hsplit := hpair _ _ hne
  have hbot : b.ExteriorAlgebra s ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm R M) 0 ⊓
        CliffordAlgebra.evenOdd (0 : QuadraticForm R M) 1 := by
    rcases hsplit with ⟨hc, hi⟩ | ⟨hc, hi⟩
    · exact ⟨hc ▸ hcard, hi ▸ hmem⟩
    · exact ⟨hi ▸ hmem, hc ▸ hcard⟩
  rw [(CliffordAlgebra.evenOdd_isCompl (Q := (0 : QuadraticForm R M))).inf_eq_bot,
    Submodule.mem_bot] at hbot
  exact b.ExteriorAlgebra.ne_zero s hbot

end Module.Basis
