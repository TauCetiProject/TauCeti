/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# The intersection algebra of a pseudoholomorphic cycle in a good class through generic points

Let `X` be a closed symplectic four-manifold with canonical class `κ` and a generic compatible
almost complex structure `J`. The virtual dimension of a class `x ∈ H₂(X; ℤ)` is
`d(x) = x · x - κ · x`, and a class `e` is *good* if `e · S ≥ -1` for every embedded
`J`-holomorphic sphere `S` of square `-1`. Suppose that `D = ∑ m_i C_i` is a positive cycle of
distinct simple `J`-holomorphic images `C_i`, with positive multiplicities `m_i`, representing a
good class `e` with `d(e) = 2k ≥ 0`, and passing through `k` generic points. The geometry of
`J`-curves supplies the following numerical facts about the classes `[C_i]` in the intersection
lattice:

* distinct images meet nonnegatively, `C_i · C_j ≥ 0` for `i ≠ j`;
* if `C_i` has singularity number `δ_i` and contains `k_i` of the generic points, then
  `2 k_i ≤ d(C_i) - 2 δ_i`, the index of the simple curves in the class of `C_i`;
* an image of negative square is an exceptional sphere, and as `e` is good it satisfies
  `e · C_i ≥ -1`;
* the classes sum to `e`, and every generic point lies on some image.

This file records these facts as `TauCeti.IsGoodCycle` on an arbitrary integral bilinear form and
derives their purely algebraic consequences, following Taubes's analysis of the curves arising
from Seiberg–Witten solutions in a good class:

* the good-curve component inequality `∑ m_i d(C_i) ≤ d(e)`, which holds for every
  combination `e = ∑ m_i C_i` with natural coefficients of classes meeting pairwise
  nonnegatively, provided `e · C_i ≥ -1` whenever `C_i · C_i < 0`;
* every image is embedded, `δ_i = 0`, and contains exactly `d(C_i) / 2` of the points;
* every point lies on exactly one image, and `d(e) = ∑ d(C_i)`;
* an image of negative square has square `-1`;
* distinct images are homologically disjoint, and exceptional spheres occur with multiplicity one;
* an image occurring with multiplicity at least two satisfies `C_i · C_i = κ · C_i = 0` and
  contains none of the points, so by adjunction it is a square-zero torus orthogonal to `κ`.

The argument expands `d(e) = ∑ m_i (d(C_i) + (e · C_i - C_i · C_i))`: each excess
`m_i (e · C_i - C_i · C_i)` is nonnegative, and comparing the result with the point count
`d(e) = 2 k ≤ ∑ 2 k_i ≤ ∑ d(C_i)` forces equality in every step.

## Main declarations

* `TauCeti.sum_mul_apply_self_sub_apply_canonical_le`: the good-curve component inequality.
* `TauCeti.IsGoodCycle`: the numerical properties of a positive cycle of simple pseudoholomorphic
  images in a good class through generic points.
* `TauCeti.IsGoodCycle.singularity_eq_zero`: every image is embedded.
* `TauCeti.IsGoodCycle.apply_self_sub_apply_canonical_eq`: every image contains half its virtual
  dimension of the points.
* `TauCeti.IsGoodCycle.existsUnique_mem`: every point lies on exactly one image.
* `TauCeti.IsGoodCycle.apply_eq_apply_self`: `e · C_i = C_i · C_i` for every image.
* `TauCeti.IsGoodCycle.apply_self_eq_neg_one`: images of negative square have square `-1`.
* `TauCeti.IsGoodCycle.apply_eq_zero`: distinct images are homologically disjoint.
* `TauCeti.IsGoodCycle.mult_eq_one_of_apply_self_neg`: exceptional spheres occur once.
* `TauCeti.IsGoodCycle.apply_self_sub_apply_canonical_eq_zero_of_one_lt_mult`,
  `TauCeti.IsGoodCycle.apply_self_eq_zero_of_one_lt_mult`,
  `TauCeti.IsGoodCycle.apply_canonical_eq_zero_of_one_lt_mult`,
  `TauCeti.IsGoodCycle.eq_empty_of_one_lt_mult`: repeated images have virtual dimension zero, are
  square-zero and orthogonal to `κ`, and avoid the points.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845--918.
* C. H. Taubes, *Seiberg–Witten and Gromov invariants for symplectic 4-manifolds*,
  First International Press Lecture Series 2 (2000).
-/

public section

open LinearMap (BilinForm)

namespace TauCeti

variable {H ι P : Type*} [AddCommGroup H] [Fintype ι]
  {B : BilinForm ℤ H} {κ e : H} {C : ι → H} {m : ι → ℕ}

/-- The pairing of `e = ∑ m j • C j` with any class, expanded over the images. -/
private theorem apply_eq_sum (he : ∑ j, m j • C j = e) (x : H) :
    B e x = ∑ j, (m j : ℤ) * B (C j) x := by
  simp [← he, map_sum, LinearMap.sum_apply, map_nsmul]

/-- The pairing of `e = ∑ m j • C j` with an image `C i`, split into the contribution of `C i`
itself and those of the other images. -/
theorem cycle_apply_eq_add_sum [DecidableEq ι] (he : ∑ j, m j • C j = e) (i : ι) :
    B e (C i) = m i * B (C i) (C i) + ∑ j ∈ Finset.univ.erase i, (m j : ℤ) * B (C j) (C i) := by
  rw [apply_eq_sum he]
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm

/-- The virtual dimension of `e = ∑ m i • C i` splits into the virtual dimensions of the images
and their excess intersections `e · C i - C i · C i` with the cycle. -/
theorem cycle_apply_self_sub_apply_canonical_eq_sum_add_sum (he : ∑ i, m i • C i = e) :
    B e e - B κ e = ∑ i, (m i : ℤ) * (B (C i) (C i) - B κ (C i)) +
      ∑ i, (m i : ℤ) * (B e (C i) - B (C i) (C i)) := by
  have hee : B e e = ∑ i, (m i : ℤ) * B e (C i) := by
    calc B e e = B e (∑ i, m i • C i) := by rw [he]
      _ = _ := by simp [map_sum, map_nsmul]
  have hκe : B κ e = ∑ i, (m i : ℤ) * B κ (C i) := by
    rw [← he]
    simp [map_sum, map_nsmul]
  rw [hee, hκe, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- An image other than `C i`, counted with its multiplicity, meets `C i` nonnegatively. -/
private theorem mul_apply_nonneg_of_mem_erase [DecidableEq ι]
    (hpos : ∀ {i j}, i ≠ j → 0 ≤ B (C i) (C j)) {i j : ι} (hj : j ∈ Finset.univ.erase i) :
    0 ≤ (m j : ℤ) * B (C j) (C i) :=
  mul_nonneg (Int.natCast_nonneg _) (hpos (Finset.ne_of_mem_erase hj))

/-- The images other than `C i`, counted with multiplicity, meet `C i` nonnegatively. -/
private theorem sum_erase_mul_apply_nonneg [DecidableEq ι]
    (hpos : ∀ {i j}, i ≠ j → 0 ≤ B (C i) (C j)) (i : ι) :
    0 ≤ ∑ j ∈ Finset.univ.erase i, (m j : ℤ) * B (C j) (C i) :=
  Finset.sum_nonneg fun _ hj ↦ mul_apply_nonneg_of_mem_erase hpos hj

/-- Each image contributes a nonnegative excess intersection `m i (e · C i - C i · C i)` to the
virtual dimension of `e = ∑ m j • C j`, provided distinct images meet nonnegatively and `e` is
at least `-1` on every image of negative square. -/
private theorem mul_apply_sub_apply_self_nonneg (he : ∑ j, m j • C j = e)
    (hpos : ∀ {i j}, i ≠ j → 0 ≤ B (C i) (C j))
    (hgood : ∀ i, B (C i) (C i) < 0 → -1 ≤ B e (C i)) (i : ι) :
    0 ≤ (m i : ℤ) * (B e (C i) - B (C i) (C i)) := by
  classical
  rcases Nat.eq_zero_or_pos (m i) with hm | hm
  · simp [hm]
  refine mul_nonneg (Int.natCast_nonneg _) ?_
  rcases lt_or_ge (B (C i) (C i)) 0 with hi | hi
  · linarith [hgood i hi]
  have hs := sum_erase_mul_apply_nonneg (m := m) hpos i
  have hm' : (1 : ℤ) ≤ m i := by exact_mod_cast hm
  rw [cycle_apply_eq_add_sum he]
  nlinarith

/-- **The good-curve component inequality.** If `e = ∑ m i • C i` is a combination with natural
coefficients of classes which meet pairwise nonnegatively, and `e` is at least `-1` on every
class `C i` of negative square (as for a good class and exceptional spheres), then the virtual
dimensions `d(x) = x · x - κ · x` satisfy `∑ m i d(C i) ≤ d(e)`. -/
theorem sum_mul_apply_self_sub_apply_canonical_le (he : ∑ i, m i • C i = e)
    (hpos : ∀ {i j}, i ≠ j → 0 ≤ B (C i) (C j))
    (hgood : ∀ i, B (C i) (C i) < 0 → -1 ≤ B e (C i)) :
    ∑ i, (m i : ℤ) * (B (C i) (C i) - B κ (C i)) ≤ B e e - B κ e := by
  rw [cycle_apply_self_sub_apply_canonical_eq_sum_add_sum he]
  exact le_add_of_nonneg_right <| Finset.sum_nonneg fun i _ ↦
    mul_apply_sub_apply_self_nonneg he hpos hgood i

/-- The numerical properties of a positive cycle `∑ m i • C i` of distinct simple
pseudoholomorphic images in a good class `e` of a symplectic four-manifold with canonical class
`κ`, passing through generic points indexed by `P`, read in the intersection form `B` on
integral homology. The image `C i` has singularity number `δ i` and contains the points `pts i`.
The fields say: the multiplicities are positive; distinct images meet nonnegatively; the number
of points on an image is at most half the index `d(C i) - 2 δ i` of simple curves in its class,
where `d(x) = x · x - κ · x`; the good class `e` is at least `-1` on every image of negative
square; the cycle represents `e`; every point lies on some image; and the number of points is
half the virtual dimension of `e`. The square `-1` of an image of negative square, which
adjunction forces for an exceptional sphere, then follows (`IsGoodCycle.apply_self_eq_neg_one`). -/
structure IsGoodCycle [Fintype P] (B : BilinForm ℤ H) (κ e : H) (C : ι → H) (m δ : ι → ℕ)
    (pts : ι → Finset P) : Prop where
  /-- Every image occurs with positive multiplicity. -/
  mult_pos : ∀ i, 0 < m i
  /-- Distinct images meet nonnegatively. -/
  apply_nonneg : ∀ {i j}, i ≠ j → 0 ≤ B (C i) (C j)
  /-- The generic points on an image cut its index `d(C) - 2 δ(C)` down to a nonnegative
  dimension. -/
  two_mul_card_add_le : ∀ i, 2 * ((pts i).card + δ i : ℤ) ≤ B (C i) (C i) - B κ (C i)
  /-- The class `e` is good: it is at least `-1` on every exceptional sphere among the images. -/
  neg_one_le_apply : ∀ i, B (C i) (C i) < 0 → -1 ≤ B e (C i)
  /-- The cycle represents `e`. -/
  sum_eq : ∑ i, m i • C i = e
  /-- Every point lies on some image. -/
  exists_mem : ∀ p, ∃ i, p ∈ pts i
  /-- The number of points is half the virtual dimension of `e`. -/
  apply_self_sub_apply_canonical : B e e - B κ e = 2 * Fintype.card P

namespace IsGoodCycle

variable [Fintype P] {δ : ι → ℕ} {pts : ι → Finset P}

/-- Every point lies on some image, so the image point counts add up to at least the number of
points. -/
private theorem card_le_sum_card (h : IsGoodCycle B κ e C m δ pts) :
    Fintype.card P ≤ ∑ i, (pts i).card := by
  classical
  calc Fintype.card P = (Finset.univ.biUnion pts).card := by
        rw [Finset.eq_univ_of_forall fun p ↦ Finset.mem_biUnion.2 (by simpa using h.exists_mem p),
          Finset.card_univ]
    _ ≤ ∑ i, (pts i).card := Finset.card_biUnion_le

/-- The equality case of the chain of inequalities `d(e) = 2 k ≤ ∑ 2 k_i ≤ ∑ d(C i) ≤ d(e)`. -/
private structure Rigid (B : BilinForm ℤ H) (κ e : H) (C : ι → H) (m δ : ι → ℕ)
    (pts : ι → Finset P) : Prop where
  /-- Every excess intersection vanishes. -/
  mul_apply_sub_apply_self_eq_zero : ∀ i, (m i : ℤ) * (B e (C i) - B (C i) (C i)) = 0
  /-- An image with multiplicity at least two has virtual dimension zero. -/
  mult_sub_one_mul_eq_zero : ∀ i, ((m i : ℤ) - 1) * (B (C i) (C i) - B κ (C i)) = 0
  /-- Every image contains half its virtual dimension of the points. -/
  apply_self_sub_apply_canonical_eq : ∀ i, B (C i) (C i) - B κ (C i) = 2 * (pts i).card
  /-- Every image is embedded. -/
  singularity_eq_zero : ∀ i, δ i = 0
  /-- The image point counts add up to the number of points. -/
  sum_card_eq : ∑ i, (pts i).card = Fintype.card P

/-- A good cycle realises the equality case of `d(e) = 2 k ≤ ∑ 2 k_i ≤ ∑ d(C i) ≤ d(e)`. -/
private theorem rigid (h : IsGoodCycle B κ e C m δ pts) : Rigid B κ e C m δ pts := by
  have hex := mul_apply_sub_apply_self_nonneg h.sum_eq h.apply_nonneg h.neg_one_le_apply
  have hmul : ∀ i, 0 ≤ ((m i : ℤ) - 1) * (B (C i) (C i) - B κ (C i)) := fun i ↦
    mul_nonneg (by linarith [(by exact_mod_cast h.mult_pos i : (1 : ℤ) ≤ m i)])
      (by linarith [h.two_mul_card_add_le i])
  have hdim : ∀ i, 0 ≤ B (C i) (C i) - B κ (C i) - 2 * ((pts i).card + δ i : ℤ) := fun i ↦ by
    linarith [h.two_mul_card_add_le i]
  have hcard : (Fintype.card P : ℤ) ≤ ∑ i, ((pts i).card : ℤ) := by
    exact_mod_cast h.card_le_sum_card
  -- Split `d(e) = ∑ m i d(C i) + ∑ m i (e · C i - C i · C i)` into nonnegative pieces.
  have hsplit : 2 * (Fintype.card P : ℤ) =
      ∑ i, (m i : ℤ) * (B e (C i) - B (C i) (C i)) +
        ∑ i, ((m i : ℤ) - 1) * (B (C i) (C i) - B κ (C i)) +
        ∑ i, (B (C i) (C i) - B κ (C i) - 2 * ((pts i).card + δ i : ℤ)) +
        2 * ∑ i, (δ i : ℤ) + 2 * ∑ i, ((pts i).card : ℤ) := by
    rw [← h.apply_self_sub_apply_canonical,
      cycle_apply_self_sub_apply_canonical_eq_sum_add_sum h.sum_eq]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have h1 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ hex i
  have h2 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ hmul i
  have h3 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ hdim i
  have h4 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ Int.natCast_nonneg (δ i)
  have z1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hex i).1 (by linarith)
  have z2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hmul i).1 (by linarith)
  have z3 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hdim i).1 (by linarith)
  have z4 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ Int.natCast_nonneg (δ i)).1
    (by linarith)
  have hδ : ∀ i, δ i = 0 := fun i ↦ by exact_mod_cast z4 i (Finset.mem_univ i)
  refine ⟨fun i ↦ z1 i (Finset.mem_univ i), fun i ↦ z2 i (Finset.mem_univ i), fun i ↦ ?_, hδ,
    by exact_mod_cast (show ∑ i, ((pts i).card : ℤ) = Fintype.card P by linarith)⟩
  linarith [z3 i (Finset.mem_univ i), hδ i]

/-- Every image is embedded: its singularity number vanishes. -/
theorem singularity_eq_zero (h : IsGoodCycle B κ e C m δ pts) (i : ι) : δ i = 0 :=
  h.rigid.singularity_eq_zero i

/-- Every image contains exactly half its virtual dimension of the points. -/
theorem apply_self_sub_apply_canonical_eq (h : IsGoodCycle B κ e C m δ pts) (i : ι) :
    B (C i) (C i) - B κ (C i) = 2 * (pts i).card :=
  h.rigid.apply_self_sub_apply_canonical_eq i

/-- The virtual dimension of `e` is the sum of the virtual dimensions of the images. -/
theorem apply_self_sub_apply_canonical_eq_sum (h : IsGoodCycle B κ e C m δ pts) :
    B e e - B κ e = ∑ i, (B (C i) (C i) - B κ (C i)) := by
  simp only [h.apply_self_sub_apply_canonical, h.apply_self_sub_apply_canonical_eq,
    ← Finset.mul_sum]
  exact_mod_cast congrArg (2 * ·) h.rigid.sum_card_eq.symm

/-- Every point lies on exactly one image. -/
theorem existsUnique_mem (h : IsGoodCycle B κ e C m δ pts) (p : P) : ∃! i, p ∈ pts i := by
  classical
  -- Count incidences point by point: each point lies on at least one image, and the total
  -- number of incidences is the number of points.
  have hswap : ∑ i, (pts i).card = ∑ q, (Finset.univ.filter fun i ↦ q ∈ pts i).card := by
    convert Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := Finset.univ) (t := Finset.univ) (r := fun i q ↦ q ∈ pts i) using 3 <;>
      simp [Finset.bipartiteAbove, Finset.bipartiteBelow]
  have hle : ∀ q ∈ Finset.univ, 1 ≤ (Finset.univ.filter fun i ↦ q ∈ pts i).card := fun q _ ↦
    Finset.card_pos.2 <| by simpa [Finset.Nonempty] using h.exists_mem q
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (by
    rw [← hswap, h.rigid.sum_card_eq, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ])
  obtain ⟨i, hi⟩ := Finset.card_eq_one.1 (heq p (Finset.mem_univ p)).symm
  refine ⟨i, by simpa using hi.ge (Finset.mem_singleton_self i), fun j hj ↦ ?_⟩
  simpa using hi.le (Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩)

/-- The class `e` pairs with every image as the image pairs with itself: `e · C i = C i · C i`.
Equivalently, the images other than `C i`, counted with multiplicity, together with
`m i - 1` copies of `C i`, pair to zero with `C i`. -/
theorem apply_eq_apply_self (h : IsGoodCycle B κ e C m δ pts) (i : ι) :
    B e (C i) = B (C i) (C i) := by
  have hm : (0 : ℤ) < m i := by exact_mod_cast h.mult_pos i
  linarith [(mul_eq_zero.1 (h.rigid.mul_apply_sub_apply_self_eq_zero i)).resolve_left hm.ne']

/-- An image of negative square has square `-1`, as an exceptional sphere does. -/
theorem apply_self_eq_neg_one (h : IsGoodCycle B κ e C m δ pts) {i : ι}
    (hi : B (C i) (C i) < 0) : B (C i) (C i) = -1 := by
  linarith [h.apply_eq_apply_self i, h.neg_one_le_apply i hi]

/-- No other image meets an image of nonnegative square, and the square of such an image
vanishes unless its multiplicity is one. -/
private theorem rigid_of_apply_self_nonneg (h : IsGoodCycle B κ e C m δ pts) {i : ι}
    (hi : 0 ≤ B (C i) (C i)) :
    (∀ j, j ≠ i → B (C j) (C i) = 0) ∧ ((m i : ℤ) - 1) * B (C i) (C i) = 0 := by
  classical
  have hm : (1 : ℤ) ≤ m i := by exact_mod_cast h.mult_pos i
  have hexp := cycle_apply_eq_add_sum (B := B) h.sum_eq i
  have hs := sum_erase_mul_apply_nonneg (m := m) h.apply_nonneg i
  have he := h.apply_eq_apply_self i
  have hsq : 0 ≤ ((m i : ℤ) - 1) * B (C i) (C i) := mul_nonneg (by linarith) hi
  have hsum : ∑ j ∈ Finset.univ.erase i, (m j : ℤ) * B (C j) (C i) = 0 := by linarith
  refine ⟨fun j hj ↦ ?_, by linarith⟩
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun _ hk ↦
    mul_apply_nonneg_of_mem_erase h.apply_nonneg hk).1 hsum j (Finset.mem_erase.2 ⟨hj, by simp⟩)
  have hmj : (0 : ℤ) < m j := by exact_mod_cast h.mult_pos j
  exact (mul_eq_zero.1 hterm).resolve_left hmj.ne'

/-- At an exceptional sphere `C a` the other images meet `C a` with total multiplicity
`m a - 1`; in particular each of them meets it at most `m a - 1` times. -/
private theorem mul_apply_le_of_apply_self_neg (h : IsGoodCycle B κ e C m δ pts) {a b : ι}
    (hab : a ≠ b) (ha : B (C a) (C a) < 0) : (m b : ℤ) * B (C b) (C a) ≤ m a - 1 := by
  classical
  have he := h.apply_eq_apply_self a
  have hexp := cycle_apply_eq_add_sum (B := B) h.sum_eq a
  rw [he, h.apply_self_eq_neg_one ha] at hexp
  have hle := Finset.single_le_sum (f := fun k ↦ (m k : ℤ) * B (C k) (C a))
    (fun _ hk ↦ mul_apply_nonneg_of_mem_erase h.apply_nonneg hk)
    (Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩)
  linarith

/-- Distinct images are homologically disjoint. -/
theorem apply_eq_zero (hB : B.IsSymm) (h : IsGoodCycle B κ e C m δ pts) {i j : ι}
    (hij : i ≠ j) : B (C i) (C j) = 0 := by
  rcases le_or_gt 0 (B (C j) (C j)) with hj | hj
  · exact (h.rigid_of_apply_self_nonneg hj).1 i hij
  rcases le_or_gt 0 (B (C i) (C i)) with hi | hi
  · rw [hB.eq]
    exact (h.rigid_of_apply_self_nonneg hi).1 j hij.symm
  -- Two exceptional spheres meeting `c ≥ 1` times would give `m i ≤ m j - 1` and
  -- `m j ≤ m i - 1`.
  have hij' := h.mul_apply_le_of_apply_self_neg hij.symm hj
  have hji := h.mul_apply_le_of_apply_self_neg hij hi
  rw [hB.eq] at hji
  have hnn := h.apply_nonneg hij
  by_contra hne
  have h1 : 1 ≤ B (C i) (C j) := by omega
  linarith [mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg (m i)),
    mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg (m j))]

/-- Every exceptional sphere occurs with multiplicity one. -/
theorem mult_eq_one_of_apply_self_neg (hB : B.IsSymm) (h : IsGoodCycle B κ e C m δ pts) {i : ι}
    (hi : B (C i) (C i) < 0) : m i = 1 := by
  classical
  have he := h.apply_eq_apply_self i
  have hexp := cycle_apply_eq_add_sum (B := B) h.sum_eq i
  rw [he, h.apply_self_eq_neg_one hi, Finset.sum_eq_zero fun j hj ↦ by
    rw [h.apply_eq_zero hB (Finset.ne_of_mem_erase hj), mul_zero]] at hexp
  omega

/-- An image occurring with multiplicity at least two has square zero. -/
theorem apply_self_eq_zero_of_one_lt_mult (hB : B.IsSymm) (h : IsGoodCycle B κ e C m δ pts)
    {i : ι} (hi : 1 < m i) : B (C i) (C i) = 0 := by
  have hsq : 0 ≤ B (C i) (C i) := not_lt.1 fun hneg ↦
    hi.ne' (h.mult_eq_one_of_apply_self_neg hB hneg)
  have hm : (1 : ℤ) < m i := by exact_mod_cast hi
  exact (mul_eq_zero.1 (h.rigid_of_apply_self_nonneg hsq).2).resolve_left (by linarith)

/-- An image occurring with multiplicity at least two has virtual dimension zero. -/
theorem apply_self_sub_apply_canonical_eq_zero_of_one_lt_mult
    (h : IsGoodCycle B κ e C m δ pts) {i : ι} (hi : 1 < m i) :
    B (C i) (C i) - B κ (C i) = 0 := by
  have hm : (1 : ℤ) < m i := by exact_mod_cast hi
  exact (mul_eq_zero.1 (h.rigid.mult_sub_one_mul_eq_zero i)).resolve_left (by linarith)

/-- An image occurring with multiplicity at least two is orthogonal to the canonical class. -/
theorem apply_canonical_eq_zero_of_one_lt_mult (hB : B.IsSymm) (h : IsGoodCycle B κ e C m δ pts)
    {i : ι} (hi : 1 < m i) : B κ (C i) = 0 := by
  linarith [h.apply_self_sub_apply_canonical_eq_zero_of_one_lt_mult hi,
    h.apply_self_eq_zero_of_one_lt_mult hB hi]

/-- An image occurring with multiplicity at least two contains none of the points. -/
theorem eq_empty_of_one_lt_mult (h : IsGoodCycle B κ e C m δ pts) {i : ι} (hi : 1 < m i) :
    pts i = ∅ := by
  have := h.apply_self_sub_apply_canonical_eq i
  rw [h.apply_self_sub_apply_canonical_eq_zero_of_one_lt_mult hi] at this
  exact Finset.card_eq_zero.1 (by omega)

end IsGoodCycle

end TauCeti
