/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Projection
public import Mathlib.Analysis.Matrix.Order
public import TauCeti.Algebra.Star.PartialIsometry

/-!
# Infinite and properly infinite projections

A projection `p` of a star-ordered ring is **infinite** (`TauCeti.IsInfiniteProjection`) if it
is Murray–von Neumann equivalent to a proper subprojection of itself: some `v` has `v⋆v = p`,
`vv⋆ ≤ p` and `vv⋆ ≠ p`. It is **properly infinite** (`TauCeti.IsProperlyInfiniteProjection`) if
it contains two orthogonal subprojections each equivalent to `p`: some `v, w` have
`v⋆v = w⋆w = p`, `vv⋆ ≤ p`, `ww⋆ ≤ p` and `vv⋆ · ww⋆ = 0` (Rørdam, §4.1).

Nonzeroness is kept explicit: `p = 0` is properly infinite but not infinite. In a ring with a
proper star (for instance a C⋆-algebra) an infinite projection is nonzero
(`TauCeti.IsInfiniteProjection.ne_zero`), while `p = 0` is properly infinite
(`TauCeti.isProperlyInfiniteProjection_zero`). A nonzero properly infinite projection is infinite
(`TauCeti.IsProperlyInfiniteProjection.isInfiniteProjection`): if `vv⋆ = p`, then `ww⋆ ≤ p` and
`p · ww⋆ = 0` force `ww⋆ = 0`, hence `w = 0` and `p = w⋆w = 0`.

Both notions are invariant under Murray–von Neumann equivalence: if `u⋆u = p` and `uu⋆ = q`,
the witnesses `v` of `p` give witnesses `u v u⋆` of `q`
(`TauCeti.IsInfiniteProjection.of_star_mul_self_eq`,
`TauCeti.IsProperlyInfiniteProjection.of_star_mul_self_eq`). Witnesses lie in the corner `q R q`
of every projection `q ≥ p` (`TauCeti.IsInfiniteProjection.exists_mul_mul_eq_self`,
`TauCeti.IsProperlyInfiniteProjection.exists_mul_mul_eq_self`), so both notions are the same
in such a corner. A properly infinite projection splits into a sequence of mutually orthogonal
subprojections each equivalent to `p` (`TauCeti.IsProperlyInfiniteProjection.exists_seq`): with
witnesses `v`, `w`, take the ranges of `wⁱ v`.

The matrix algebra `M_n(𝕜)` over `𝕜 = ℝ` or `ℂ` has no infinite projection
(`Matrix.not_isInfiniteProjection`): `p - vv⋆` is positive semidefinite with trace
`tr(v⋆v) - tr(vv⋆) = 0`, so `vv⋆ = p`.

## References

* Rørdam, Part I of Rørdam–Størmer, *Classification of Nuclear C*-Algebras. Entropy in Operator
  Algebras*, Encyclopaedia of Mathematical Sciences 126, Springer, 2002, §4.1.
-/

public section

namespace TauCeti

variable {R : Type*} [NonUnitalRing R] [StarRing R] [PartialOrder R]

/-- A projection `p` is **infinite** if it is Murray–von Neumann equivalent to a proper
subprojection: some `v` has `v⋆v = p`, `vv⋆ ≤ p` and `vv⋆ ≠ p`. -/
def IsInfiniteProjection (p : R) : Prop :=
  IsStarProjection p ∧ ∃ v : R, star v * v = p ∧ v * star v ≤ p ∧ v * star v ≠ p

/-- A projection `p` is **properly infinite** if it contains two orthogonal subprojections each
Murray–von Neumann equivalent to `p`. The zero projection is properly infinite. -/
def IsProperlyInfiniteProjection (p : R) : Prop :=
  IsStarProjection p ∧ ∃ v w : R, star v * v = p ∧ star w * w = p ∧
    v * star v ≤ p ∧ w * star w ≤ p ∧ v * star v * (w * star w) = 0

/-- Unfold the definition of an infinite projection. -/
theorem isInfiniteProjection_iff {p : R} : IsInfiniteProjection p ↔
    IsStarProjection p ∧ ∃ v : R, star v * v = p ∧ v * star v ≤ p ∧ v * star v ≠ p :=
  Iff.rfl

/-- Unfold the definition of a properly infinite projection. -/
theorem isProperlyInfiniteProjection_iff {p : R} : IsProperlyInfiniteProjection p ↔
    IsStarProjection p ∧ ∃ v w : R, star v * v = p ∧ star w * w = p ∧
      v * star v ≤ p ∧ w * star w ≤ p ∧ v * star v * (w * star w) = 0 :=
  Iff.rfl

/-- An infinite projection is a star projection. -/
theorem IsInfiniteProjection.isStarProjection {p : R} (hp : IsInfiniteProjection p) :
    IsStarProjection p :=
  hp.1

/-- A properly infinite projection is a star projection. -/
theorem IsProperlyInfiniteProjection.isStarProjection {p : R}
    (hp : IsProperlyInfiniteProjection p) : IsStarProjection p :=
  hp.1

/-- The zero projection is properly infinite, with `v = w = 0`. -/
@[simp]
theorem isProperlyInfiniteProjection_zero : IsProperlyInfiniteProjection (0 : R) :=
  ⟨.zero R, 0, 0, by simp⟩

/-- An infinite projection is nonzero. -/
theorem IsInfiniteProjection.ne_zero [IsProperStar R] {p : R} (hp : IsInfiniteProjection p) :
    p ≠ 0 := by
  rintro rfl
  obtain ⟨-, v, hv, -, hne⟩ := hp
  rw [star_mul_self_eq_zero] at hv
  simp [hv] at hne

/-- The zero projection is not infinite, although it is properly infinite. -/
@[simp]
theorem not_isInfiniteProjection_zero [IsProperStar R] : ¬ IsInfiniteProjection (0 : R) :=
  fun h ↦ h.ne_zero rfl

variable [StarOrderedRing R] [IsProperStar R]

/-- A nonzero properly infinite projection is infinite. -/
theorem IsProperlyInfiniteProjection.isInfiniteProjection {p : R}
    (h : IsProperlyInfiniteProjection p) (hp : p ≠ 0) : IsInfiniteProjection p := by
  obtain ⟨hpp, v, w, hv, hw, hvp, hwp, hvw⟩ := h
  refine ⟨hpp, v, hv, hvp, fun hvv ↦ hp ?_⟩
  have hwproj := (isPartialIsometry_iff_isStarProjection_star_mul_self.mpr
    (hw ▸ hpp)).isStarProjection_mul_star_self
  have hw0 : w * star w = 0 := by
    rw [← (hwproj.le_iff_mul_eq_right hpp).mp hwp, ← hvv, hvw]
  rw [mul_star_self_eq_zero] at hw0
  rw [← hw, hw0, star_zero, zero_mul]

/-! ### Permanence under equivalence and splitting -/

/-- If `v⋆v = p` is a projection and `vv⋆ ≤ p`, then `p v = v` and `v p = v`. -/
private theorem mul_eq_self_and_eq_mul_self {p v : R} (hp : IsStarProjection p)
    (hv : star v * v = p) (hvp : v * star v ≤ p) : p * v = v ∧ v * p = v := by
  have hpi : IsPartialIsometry v :=
    isPartialIsometry_iff_isStarProjection_star_mul_self.mpr (hv ▸ hp)
  have hle := (hpi.isStarProjection_mul_star_self.le_iff_mul_eq_right hp).mp hvp
  refine ⟨?_, by rw [← hv, ← mul_assoc]; exact hpi.mul_star_mul_self⟩
  rw [← hpi.mul_star_mul_self, ← mul_assoc, ← mul_assoc, mul_assoc p v, hle]

/-- Conjugating a witness: if `u⋆u = p`, `uu⋆ = q`, `v⋆v = p` and `vv⋆ ≤ p`, then `w = u v u⋆`
has `w⋆w = q`, `ww⋆ = u (vv⋆) u⋆` and `ww⋆ ≤ q`. -/
private theorem conj_witness {p q u v : R} (hp : IsStarProjection p) (hu : star u * u = p)
    (hu' : u * star u = q) (hv : star v * v = p) (hvp : v * star v ≤ p) :
    star (u * v * star u) * (u * v * star u) = q ∧
      u * v * star u * star (u * v * star u) = u * (v * star v) * star u ∧
      u * v * star u * star (u * v * star u) ≤ q := by
  obtain ⟨hpv, hvp'⟩ := mul_eq_self_and_eq_mul_self hp hv hvp
  have hup : u * p = u := by
    rw [← hu, ← mul_assoc]
    exact (isPartialIsometry_iff_isStarProjection_star_mul_self.mpr (hu ▸ hp)).mul_star_mul_self
  have hqe : u * p * star u = q := by rw [hup, hu']
  have h₂ : u * v * star u * star (u * v * star u) = u * (v * star v) * star u := by
    calc _ = u * (v * (star u * u) * star v) * star u := by
          simp only [star_mul, star_star, mul_assoc]
      _ = _ := by rw [hu, hvp']
  refine ⟨?_, h₂, ?_⟩
  · calc _ = u * (star v * (star u * u) * v) * star u := by
          simp only [star_mul, star_star, mul_assoc]
      _ = q := by rw [hu, mul_assoc (star v), hpv, hv, hqe]
  · rw [h₂, ← hqe]
    exact star_right_conjugate_le_conjugate hvp u

/-- **Infiniteness is invariant under Murray–von Neumann equivalence**: if `u⋆u = p` and
`uu⋆ = q` with `p` infinite, then `q` is infinite, witnessed by `u v u⋆`. -/
theorem IsInfiniteProjection.of_star_mul_self_eq {p q u : R} (hp : IsInfiniteProjection p)
    (hu : star u * u = p) (hu' : u * star u = q) : IsInfiniteProjection q := by
  obtain ⟨hpp, v, hv, hvp, hne⟩ := hp
  obtain ⟨h₁, h₂, h₃⟩ := conj_witness hpp hu hu' hv hvp
  have hq : IsStarProjection q := hu' ▸ (isPartialIsometry_iff_isStarProjection_star_mul_self.mpr
    (hu ▸ hpp)).isStarProjection_mul_star_self
  refine ⟨hq, _, h₁, h₃, fun h ↦ hne ?_⟩
  -- Compress `u (vv⋆) u⋆ = q` back by `x ↦ u⋆ x u`, giving `p (vv⋆) p = p p p`.
  obtain ⟨hpv, -⟩ := mul_eq_self_and_eq_mul_self hpp hv hvp
  have hvp' : star v * p = star v := by
    rw [← hpp.isSelfAdjoint.star_eq, ← star_mul, hpv]
  have e₁ : star u * (u * (v * star v) * star u) * u = v * star v := by
    calc _ = (star u * u) * (v * star v) * (star u * u) := by simp only [mul_assoc]
      _ = _ := by rw [hu, ← mul_assoc, hpv, mul_assoc, hvp']
  have e₂ : star u * q * u = p := by
    rw [← hu', ← mul_assoc, hu, mul_assoc, hu, hpp.isIdempotentElem.eq]
  rw [← e₁, ← h₂, h, e₂]

/-- **Proper infiniteness is invariant under Murray–von Neumann equivalence**: if `u⋆u = p` and
`uu⋆ = q` with `p` properly infinite, then `q` is properly infinite, witnessed by `u v u⋆` and
`u w u⋆`. -/
theorem IsProperlyInfiniteProjection.of_star_mul_self_eq {p q u : R}
    (hp : IsProperlyInfiniteProjection p) (hu : star u * u = p) (hu' : u * star u = q) :
    IsProperlyInfiniteProjection q := by
  obtain ⟨hpp, v, w, hv, hw, hvp, hwp, hvw⟩ := hp
  obtain ⟨hv₁, hv₂, hv₃⟩ := conj_witness hpp hu hu' hv hvp
  obtain ⟨hw₁, hw₂, hw₃⟩ := conj_witness hpp hu hu' hw hwp
  have hq : IsStarProjection q := hu' ▸ (isPartialIsometry_iff_isStarProjection_star_mul_self.mpr
    (hu ▸ hpp)).isStarProjection_mul_star_self
  refine ⟨hq, _, _, hv₁, hw₁, hv₃, hw₃, ?_⟩
  -- `(u (vv⋆) u⋆) (u (ww⋆) u⋆) = u (vv⋆) p (ww⋆) u⋆ = u (vv⋆) (ww⋆) u⋆ = 0`.
  have hvvp : v * star v * p = v * star v := by
    rw [mul_assoc, ← hpp.isSelfAdjoint.star_eq, ← star_mul,
      (mul_eq_self_and_eq_mul_self hpp hv hvp).1]
  rw [hv₂, hw₂]
  calc _ = u * (v * star v * (star u * u) * (w * star w)) * star u := by
        simp only [mul_assoc]
    _ = 0 := by rw [hu, hvvp, hvw, mul_zero, zero_mul]

/-- A witness `v` for a subprojection of `p` lies in the corner `q R q` of every projection
`q ≥ p`: `q v q = v`. -/
private theorem mul_mul_eq_self {p q v : R} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : p ≤ q) (hv : star v * v = p) (hvp : v * star v ≤ p) : q * v * q = v := by
  obtain ⟨hpv, hvp'⟩ := mul_eq_self_and_eq_mul_self hp hv hvp
  have hqp : q * p = p := (hp.le_iff_mul_eq_right hq).mp hpq
  have hpq' : p * q = p := by
    rw [← hp.isSelfAdjoint.star_eq, ← hq.isSelfAdjoint.star_eq, ← star_mul, hqp]
  rw [← hpv, ← mul_assoc, hqp, hpv, ← hvp', mul_assoc, hpq']

/-- **Infiniteness in corners**: an infinite projection `p` is infinite in the corner `q R q` of
every projection `q ≥ p`, that is, it has a witness `v` with `q v q = v`. -/
theorem IsInfiniteProjection.exists_mul_mul_eq_self {p q : R} (hp : IsInfiniteProjection p)
    (hq : IsStarProjection q) (hpq : p ≤ q) :
    ∃ v : R, q * v * q = v ∧ star v * v = p ∧ v * star v ≤ p ∧ v * star v ≠ p := by
  obtain ⟨hpp, v, hv, hvp, hne⟩ := hp
  exact ⟨v, mul_mul_eq_self hpp hq hpq hv hvp, hv, hvp, hne⟩

/-- **Proper infiniteness in corners**: a properly infinite projection `p` is properly infinite in
the corner `q R q` of every projection `q ≥ p`, that is, it has witnesses `v`, `w` with
`q v q = v` and `q w q = w`. -/
theorem IsProperlyInfiniteProjection.exists_mul_mul_eq_self {p q : R}
    (hp : IsProperlyInfiniteProjection p) (hq : IsStarProjection q) (hpq : p ≤ q) :
    ∃ v w : R, q * v * q = v ∧ q * w * q = w ∧ star v * v = p ∧ star w * w = p ∧
      v * star v ≤ p ∧ w * star w ≤ p ∧ v * star v * (w * star w) = 0 := by
  obtain ⟨hpp, v, w, hv, hw, hvp, hwp, hvw⟩ := hp
  exact ⟨v, w, mul_mul_eq_self hpp hq hpq hv hvp, mul_mul_eq_self hpp hq hpq hw hwp, hv, hw, hvp,
    hwp, hvw⟩

/-- **Splitting a properly infinite projection**: a properly infinite projection `p` contains a
sequence of mutually orthogonal subprojections each equivalent to `p`. With witnesses `v`, `w`,
the `i`-th one is `fᵢ fᵢ⋆` for `fᵢ = wⁱ v`. -/
theorem IsProperlyInfiniteProjection.exists_seq {p : R} (hp : IsProperlyInfiniteProjection p) :
    ∃ f : ℕ → R, (∀ i, star (f i) * f i = p) ∧ (∀ i, f i * star (f i) ≤ p) ∧
      Pairwise fun i j ↦ f i * star (f i) * (f j * star (f j)) = 0 := by
  obtain ⟨hpp, v, w, hv, hw, hvp, hwp, hvw⟩ := hp
  obtain ⟨hpv, -⟩ := mul_eq_self_and_eq_mul_self hpp hv hvp
  obtain ⟨hpw, hwp'⟩ := mul_eq_self_and_eq_mul_self hpp hw hwp
  set f : ℕ → R := fun i ↦ (w * ·)^[i] v
  have hsucc (i : ℕ) : f (i + 1) = w * f i := Function.iterate_succ_apply' _ _ _
  have hpf (i : ℕ) : p * f i = f i := by
    cases i with
    | zero => exact hpv
    | succ i => rw [hsucc, ← mul_assoc, hpw]
  have hstar (i : ℕ) : star (f i) * f i = p := by
    induction i with
    | zero => exact hv
    | succ i ih =>
      rw [hsucc, star_mul, mul_assoc, ← mul_assoc (star w), hw, hpf, ih]
  have hle (i : ℕ) : f i * star (f i) ≤ p := by
    induction i with
    | zero => exact hvp
    | succ i ih =>
      rw [hsucc, star_mul, ← mul_assoc, mul_assoc w]
      exact (star_right_conjugate_le_conjugate ih w).trans (by rw [hwp']; exact hwp)
  -- `v⋆ w = v⋆ (vv⋆) (ww⋆) w = 0`.
  have hvw' : star v * w = 0 := by
    have h₁ : star v * v * star v = star v := by
      simpa using (isPartialIsometry_star_iff.mpr
        (isPartialIsometry_iff_isStarProjection_star_mul_self.mpr (hv ▸ hpp))).mul_star_mul_self
    have h₂ : w * star w * w = w :=
      (isPartialIsometry_iff_isStarProjection_star_mul_self.mpr (hw ▸ hpp)).mul_star_mul_self
    calc star v * w = star v * v * star v * (w * star w * w) := by rw [h₁, h₂]
      _ = star v * (v * star v * (w * star w)) * w := by simp only [mul_assoc]
      _ = 0 := by rw [hvw, mul_zero, zero_mul]
  -- `fᵢ⋆ fᵢ₊ₖ₊₁ = 0`, by induction on `i`.
  have horth (i k : ℕ) : star (f i) * f (i + k + 1) = 0 := by
    induction i with
    | zero =>
      rw [zero_add, hsucc]
      change star v * (w * f k) = 0
      rw [← mul_assoc, hvw', zero_mul]
    | succ i ih =>
      rw [show i + 1 + k + 1 = i + k + 1 + 1 by omega, hsucc, hsucc, star_mul, mul_assoc,
        ← mul_assoc (star w), hw, hpf, ih]
  have key (i j : ℕ) (h : i < j) : f i * star (f i) * (f j * star (f j)) = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
    rw [mul_assoc, ← mul_assoc (star (f i)), horth, zero_mul, mul_zero]
  refine ⟨f, hstar, hle, fun i j hij ↦ ?_⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · simpa [star_mul, mul_assoc] using congrArg star (key j i h)

/-! ### Matrix algebras -/

open scoped MatrixOrder

/-- The matrix algebra `M_n(𝕜)` has no infinite projection. -/
theorem _root_.Matrix.not_isInfiniteProjection {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]
    (p : _root_.Matrix n n 𝕜) : ¬ IsInfiniteProjection p := by
  -- `p - vv⋆` is positive semidefinite of trace `tr(v⋆v) - tr(vv⋆) = 0`, so `vv⋆ = p`.
  rintro ⟨-, v, hv, hle, hne⟩
  refine hne (sub_eq_zero.mp ?_).symm
  refine ((_root_.Matrix.le_iff.mp hle).trace_eq_zero_iff).mp ?_
  rw [_root_.Matrix.trace_sub, ← hv, _root_.Matrix.trace_mul_comm, sub_self]

end TauCeti
