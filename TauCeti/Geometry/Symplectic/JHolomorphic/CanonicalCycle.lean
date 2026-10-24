/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The intersection algebra of a pseudoholomorphic cycle in the canonical class

Let `X` be a closed symplectic four-manifold with canonical class `κ` and a compatible almost
complex structure `J`, and let `D = ∑ m_i C_i` be a positive cycle of distinct simple
`J`-holomorphic images `C_i` with positive multiplicities `m_i` whose total homology class is
Poincaré dual to `κ`. Such a cycle arises by combining the curves extracted from the
Seiberg–Witten solutions of a class `e` and of its conjugate `κ - e`. The geometry of `J`-curves
supplies four numerical facts about the classes `[C_i]` in the intersection lattice:

* distinct images meet nonnegatively, `C_i · C_j ≥ 0` for `i ≠ j`;
* each image has nonnegative virtual dimension `d(C_i) = C_i · C_i - κ · C_i ≥ 0`, since the
  index of a simple curve is `d(C) - 2 δ(C) ≥ 0`, where `δ(C) ≥ 0` is its singularity number;
* an image of negative square is an exceptional sphere, `C_i · C_i = κ · C_i = -1`;
* the classes sum to the canonical class, `∑ m_i [C_i] = κ`.

This file records these facts as `TauCeti.IsCanonicalCycle` on an arbitrary integral bilinear
form `B` and derives their purely algebraic consequences, following Taubes's analysis of canonical
cycles. Symmetry of `B`, as for the intersection form, is not part of the structure: it is an
explicit hypothesis `B.IsSymm` of every theorem below except
`TauCeti.IsCanonicalCycle.apply_canonical_eq_apply_self` and
`TauCeti.IsCanonicalCycle.exists_eq_of_apply_canonical_neg`. The consequences are:

* distinct images are homologically disjoint, `C_i · C_j = 0`;
* every image has virtual dimension zero, `κ · C_i = C_i · C_i`, and moreover
  `κ · C_i = m_i (C_i · C_i)`;
* every exceptional sphere occurs with multiplicity one;
* an image occurring with multiplicity at least two satisfies `C_i · C_i = κ · C_i = 0`, so by
  adjunction it is a square-zero torus orthogonal to `κ`;
* every subcycle `e = ∑ a_i C_i` with `a_i ≤ m_i` has virtual dimension zero;
* for every class `S` with `κ · S < 0` which each image either equals or meets nonnegatively,
  in particular for every `J`-holomorphic exceptional sphere by positivity of intersections,
  `e · S` is `0` or `-1`.

The last statement is the numerical input to the vanishing of the Seiberg–Witten point invariant
of a class `e` that is not good, i.e. which pairs below `-1` with some `J`-holomorphic
exceptional sphere.

The argument is local in each image: evaluating `κ = ∑ m_j C_j` on an image `C_i` of nonnegative
square and comparing with `d(C_i) ≥ 0` forces `(m_i - 1) C_i · C_i` and every `C_j · C_i` with
`j ≠ i` to vanish; an exceptional sphere then meets no other image, which fixes its multiplicity.

## Main declarations

* `TauCeti.IsCanonicalCycle`: the numerical properties of a positive cycle of simple
  pseudoholomorphic images in the canonical class.
* `TauCeti.IsCanonicalCycle.apply_eq_zero_of_ne`: distinct images are homologically disjoint.
* `TauCeti.IsCanonicalCycle.apply_canonical_eq_apply_self`: every image has virtual dimension
  zero.
* `TauCeti.IsCanonicalCycle.mult_eq_one_of_apply_self_neg`: exceptional spheres occur once.
* `TauCeti.IsCanonicalCycle.apply_self_eq_zero_of_one_lt_mult`,
  `TauCeti.IsCanonicalCycle.apply_canonical_eq_zero_of_one_lt_mult`: repeated images are
  square-zero and orthogonal to `κ`.
* `TauCeti.IsCanonicalCycle.apply_canonical_sum_eq_apply_self`: every subcycle has virtual
  dimension zero.
* `TauCeti.IsCanonicalCycle.apply_sum_eq_zero_or_eq_neg_one`: every subcycle pairs to `0` or `-1`
  with every `J`-holomorphic exceptional sphere.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845--918.
* C. H. Taubes, *Seiberg–Witten and Gromov invariants for symplectic 4-manifolds*,
  First International Press Lecture Series 2 (2000).
-/

public section

open LinearMap (BilinForm)

namespace TauCeti

variable {H ι : Type*} [AddCommGroup H] [Fintype ι]

/-- The numerical properties of a positive cycle `∑ m i • C i` of distinct simple
pseudoholomorphic images in the canonical class `κ` of a symplectic four-manifold, read in the
intersection form `B` on integral homology: the multiplicities are positive, distinct images meet
nonnegatively, every image has nonnegative virtual dimension `C · C - κ · C`, every image of
negative square is an exceptional sphere, and the cycle represents `κ`. -/
structure IsCanonicalCycle (B : BilinForm ℤ H) (κ : H) (C : ι → H) (m : ι → ℕ) : Prop where
  /-- Every image occurs with positive multiplicity. -/
  mult_pos : ∀ i, 0 < m i
  /-- Distinct images meet nonnegatively. -/
  apply_nonneg_of_ne : ∀ {i j}, i ≠ j → 0 ≤ B (C i) (C j)
  /-- Every image has nonnegative virtual dimension `C · C - κ · C`. -/
  apply_canonical_le_apply_self : ∀ i, B κ (C i) ≤ B (C i) (C i)
  /-- An image of negative square is an exceptional sphere: its square is `-1`. -/
  apply_self_eq_neg_one_of_apply_self_neg : ∀ i, B (C i) (C i) < 0 → B (C i) (C i) = -1
  /-- An image of negative square is an exceptional sphere: it pairs with `κ` to `-1`. -/
  apply_canonical_eq_neg_one_of_apply_self_neg : ∀ i, B (C i) (C i) < 0 → B κ (C i) = -1
  /-- The cycle represents the canonical class. -/
  sum_eq : ∑ i, m i • C i = κ

namespace IsCanonicalCycle

variable {B : BilinForm ℤ H} {κ : H} {C : ι → H} {m : ι → ℕ}

/-- The pairing of the canonical class with any class, expanded over the images of the cycle. -/
private theorem apply_canonical_eq_sum (h : IsCanonicalCycle B κ C m) (x : H) :
    B κ x = ∑ j, (m j : ℤ) * B (C j) x := by
  simp [← h.sum_eq, map_sum, LinearMap.sum_apply, map_nsmul]

/-- The pairing of the canonical class with an image `C i`, split into the contribution of
`C i` itself and those of the other images. -/
private theorem apply_canonical_eq_add_sum [DecidableEq ι] (h : IsCanonicalCycle B κ C m)
    (i : ι) :
    B κ (C i) = m i * B (C i) (C i) + ∑ j ∈ Finset.univ.erase i, (m j : ℤ) * B (C j) (C i) := by
  rw [h.apply_canonical_eq_sum]
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm

/-- The images other than `C i` meet `C i` nonnegatively in total. -/
private theorem sum_erase_nonneg [DecidableEq ι] (h : IsCanonicalCycle B κ C m) (i : ι) :
    0 ≤ ∑ j ∈ Finset.univ.erase i, (m j : ℤ) * B (C j) (C i) :=
  Finset.sum_nonneg fun _ hj ↦
    mul_nonneg (Int.natCast_nonneg _) (h.apply_nonneg_of_ne (Finset.ne_of_mem_erase hj))

/-- The local rigidity at an image of nonnegative square: no other image meets it, and its
square vanishes unless its multiplicity is one. -/
private theorem rigid_of_apply_self_nonneg (h : IsCanonicalCycle B κ C m) {i : ι}
    (hi : 0 ≤ B (C i) (C i)) :
    (∀ j, j ≠ i → B (C j) (C i) = 0) ∧ ((m i : ℤ) - 1) * B (C i) (C i) = 0 := by
  classical
  have hκ := h.apply_canonical_eq_add_sum i
  have hd := h.apply_canonical_le_apply_self i
  have hs := h.sum_erase_nonneg i
  have hm : (1 : ℤ) ≤ m i := by exact_mod_cast h.mult_pos i
  have hsq : 0 ≤ ((m i : ℤ) - 1) * B (C i) (C i) := mul_nonneg (by linarith) hi
  have hsum : ∑ j ∈ Finset.univ.erase i, (m j : ℤ) * B (C j) (C i) = 0 := by nlinarith
  refine ⟨fun j hj ↦ ?_, by nlinarith⟩
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun k hk ↦ mul_nonneg (Int.natCast_nonneg _)
    (h.apply_nonneg_of_ne (Finset.ne_of_mem_erase hk))).1 hsum j (Finset.mem_erase.2 ⟨hj, by simp⟩)
  have hmj : (0 : ℤ) < m j := by exact_mod_cast h.mult_pos j
  exact (mul_eq_zero.1 hterm).resolve_left hmj.ne'

/-- Two distinct exceptional spheres of a canonical cycle do not meet. -/
private theorem apply_eq_zero_of_apply_self_neg (hB : B.IsSymm) (h : IsCanonicalCycle B κ C m)
    {i j : ι} (hij : i ≠ j) (hi : B (C i) (C i) < 0) (hj : B (C j) (C j) < 0) :
    B (C i) (C j) = 0 := by
  classical
  -- Pairing `κ = ∑ m_k C_k` with `C_i` gives `m_i - 1 = ∑_{k ≠ i} m_k C_k · C_i`, which is at
  -- least `m_j` if the two spheres meet; symmetrically `m_j - 1 ≥ m_i`, which is absurd.
  have bound : ∀ {a b : ι}, a ≠ b → B (C a) (C a) < 0 →
      (m b : ℤ) * B (C b) (C a) ≤ m a - 1 := fun {a b} hab ha ↦ by
    have hκ := h.apply_canonical_eq_add_sum a
    rw [h.apply_canonical_eq_neg_one_of_apply_self_neg a ha,
      h.apply_self_eq_neg_one_of_apply_self_neg a ha] at hκ
    have hle := Finset.single_le_sum (f := fun k ↦ (m k : ℤ) * B (C k) (C a))
      (fun k hk ↦ mul_nonneg (Int.natCast_nonneg _)
        (h.apply_nonneg_of_ne (Finset.ne_of_mem_erase hk)))
      (Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩)
    linarith
  rw [hB.eq]
  have hij' := bound hij hi
  have hji := bound hij.symm hj
  rw [hB.eq] at hji
  have hnn := h.apply_nonneg_of_ne hij.symm
  by_contra hne
  have h1 : 1 ≤ B (C j) (C i) := by omega
  linarith [mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg (m i)),
    mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg (m j))]

/-- Distinct images of a canonical cycle are homologically disjoint. -/
theorem apply_eq_zero_of_ne (hB : B.IsSymm) (h : IsCanonicalCycle B κ C m) {i j : ι} (hij : i ≠ j) :
    B (C i) (C j) = 0 := by
  rcases le_or_gt 0 (B (C j) (C j)) with hj | hj
  · exact (h.rigid_of_apply_self_nonneg hj).1 i hij
  rcases le_or_gt 0 (B (C i) (C i)) with hi | hi
  · rw [hB.eq]
    exact (h.rigid_of_apply_self_nonneg hi).1 j hij.symm
  · exact h.apply_eq_zero_of_apply_self_neg hB hij hi hj

/-- The canonical class pairs with an image `C i` of a canonical cycle to `m i` times its
square. -/
theorem apply_canonical_eq_mul (hB : B.IsSymm) (h : IsCanonicalCycle B κ C m) (i : ι) :
    B κ (C i) = m i * B (C i) (C i) := by
  classical
  rw [h.apply_canonical_eq_add_sum, Finset.sum_eq_zero fun j hj ↦ by
    rw [h.apply_eq_zero_of_ne hB (Finset.ne_of_mem_erase hj), mul_zero], add_zero]

/-- Every image of a canonical cycle has virtual dimension zero: `κ · C = C · C`. -/
theorem apply_canonical_eq_apply_self (h : IsCanonicalCycle B κ C m) (i : ι) :
    B κ (C i) = B (C i) (C i) := by
  classical
  rcases lt_or_ge (B (C i) (C i)) 0 with hi | hi
  · rw [h.apply_canonical_eq_neg_one_of_apply_self_neg i hi,
      h.apply_self_eq_neg_one_of_apply_self_neg i hi]
  · obtain ⟨hzero, hmul⟩ := h.rigid_of_apply_self_nonneg hi
    rw [h.apply_canonical_eq_add_sum, Finset.sum_eq_zero fun j hj ↦ by
      rw [hzero j (Finset.ne_of_mem_erase hj), mul_zero]]
    linarith

/-- Every exceptional sphere of a canonical cycle occurs with multiplicity one. -/
theorem mult_eq_one_of_apply_self_neg (hB : B.IsSymm) (h : IsCanonicalCycle B κ C m) {i : ι}
    (hi : B (C i) (C i) < 0) : m i = 1 := by
  have := h.apply_canonical_eq_mul hB i
  rw [h.apply_canonical_eq_neg_one_of_apply_self_neg i hi,
    h.apply_self_eq_neg_one_of_apply_self_neg i hi] at this
  omega

/-- An image occurring with multiplicity at least two in a canonical cycle has square zero. -/
theorem apply_self_eq_zero_of_one_lt_mult (hB : B.IsSymm) (h : IsCanonicalCycle B κ C m) {i : ι}
    (hi : 1 < m i) : B (C i) (C i) = 0 := by
  have hmul := h.apply_canonical_eq_mul hB i
  rw [h.apply_canonical_eq_apply_self] at hmul
  have hm : (1 : ℤ) < m i := by exact_mod_cast hi
  have : ((m i : ℤ) - 1) * B (C i) (C i) = 0 := by linarith
  exact (mul_eq_zero.1 this).resolve_left (by linarith)

/-- An image occurring with multiplicity at least two in a canonical cycle is orthogonal to the
canonical class. -/
theorem apply_canonical_eq_zero_of_one_lt_mult (hB : B.IsSymm) (h : IsCanonicalCycle B κ C m)
    {i : ι} (hi : 1 < m i) : B κ (C i) = 0 := by
  rw [h.apply_canonical_eq_apply_self, h.apply_self_eq_zero_of_one_lt_mult hB hi]

/-- A combination `∑ a j • C j` of the images of a canonical cycle pairs with an image `C i` to
`a i` times its square. -/
theorem apply_sum_eq_mul (hB : B.IsSymm) (h : IsCanonicalCycle B κ C m) (a : ι → ℕ) (i : ι) :
    B (∑ j, a j • C j) (C i) = a i * B (C i) (C i) := by
  simp only [map_sum, LinearMap.sum_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [h.apply_eq_zero_of_ne hB hj, mul_zero])
    (by simp)]

/-- Every subcycle `e = ∑ a i • C i`, `a ≤ m`, of a canonical cycle has virtual dimension zero:
`κ · e = e · e`. -/
theorem apply_canonical_sum_eq_apply_self (hB : B.IsSymm) (h : IsCanonicalCycle B κ C m)
    {a : ι → ℕ} (ha : ∀ i, a i ≤ m i) :
    B κ (∑ i, a i • C i) = B (∑ i, a i • C i) (∑ i, a i • C i) := by
  simp only [map_sum (B _), map_nsmul, nsmul_eq_mul, h.apply_sum_eq_mul hB,
    h.apply_canonical_eq_mul hB]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases lt_or_ge 1 (m i) with hi | hi
  · rw [h.apply_self_eq_zero_of_one_lt_mult hB hi]
    simp
  · have : a i = 0 ∨ a i = 1 := by have := ha i; omega
    have hm : m i = 1 := by have := h.mult_pos i; omega
    rcases this with ha0 | ha1
    · simp [ha0]
    · simp [ha1, hm]

/-- Every class `S` on which the canonical class is negative, and which each image of a
canonical cycle either equals or meets nonnegatively, is the class of one of the images. -/
theorem exists_eq_of_apply_canonical_neg (h : IsCanonicalCycle B κ C m) {S : H}
    (hS : B κ S < 0) (hpos : ∀ i, C i = S ∨ 0 ≤ B (C i) S) : ∃ i, C i = S := by
  by_contra hne
  simp only [not_exists] at hne
  refine hS.not_ge ?_
  rw [h.apply_canonical_eq_sum]
  exact Finset.sum_nonneg fun i _ ↦
    mul_nonneg (Int.natCast_nonneg _) ((hpos i).resolve_left (hne i))

/-- A subcycle `e = ∑ a i • C i`, `a ≤ m`, of a canonical cycle pairs to `0` or `-1` with every
class `S` on which the canonical class is negative and which each image either equals or meets
nonnegatively; in particular with every `J`-holomorphic exceptional sphere. -/
theorem apply_sum_eq_zero_or_eq_neg_one (hB : B.IsSymm) (h : IsCanonicalCycle B κ C m)
    {a : ι → ℕ} (ha : ∀ i, a i ≤ m i) {S : H} (hS : B κ S < 0)
    (hpos : ∀ i, C i = S ∨ 0 ≤ B (C i) S) :
    B (∑ i, a i • C i) S = 0 ∨ B (∑ i, a i • C i) S = -1 := by
  obtain ⟨i, rfl⟩ := h.exists_eq_of_apply_canonical_neg hS hpos
  have hneg : B (C i) (C i) < 0 := by rwa [← h.apply_canonical_eq_apply_self]
  have hm := h.mult_eq_one_of_apply_self_neg hB hneg
  rw [h.apply_sum_eq_mul hB, h.apply_self_eq_neg_one_of_apply_self_neg i hneg]
  have : a i = 0 ∨ a i = 1 := by have := ha i; omega
  rcases this with ha0 | ha1
  · simp [ha0]
  · simp [ha1]

end IsCanonicalCycle

end TauCeti
