/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Fibre
public import TauCeti.Combinatorics.Young.LittlewoodRichardson.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The hive-to-Littlewood–Richardson equivalence

In the **product chart** `Vertex.productVertex n i j` (`0 ≤ i ≤ j ≤ n` mapped to the barycentric
point `(n - j, j - i, i)` of `Δₙ`), the three perimeter sides align directly with the product
boundary `(λ, μ, γ*)`:
* `i = 0` runs clockwise along `A → B`, where successive differences record `λ`;
* `j = n` runs clockwise along `B → C`, where successive differences record `μ`;
* the diagonal `i = j` runs counterclockwise along `A → C` (the reverse of `C → A`), so successive
  diagonal values record prefix sums of `γ`.

Every unit rhombus in `Δₙ` belongs to one of three orientations in `(i, j)` coordinates
(`TauCeti.Hive.isRhombusConcave_iff_productVertex`), identifying hive concavity with the three
defining conditions of a Littlewood–Richardson tableau `T` of skew shape `γ / λ` and content `μ`
via the row-letter counts `a(r, k) = T.rowCount r k`:
1. **Off-diagonal mixed differences** (`0 ≤ k < r < n`):
   `h(k + 1, r) + h(k, r + 1) ≤ h(k, r) + h(k + 1, r + 1)` expresses nonnegativity of the mixed
   difference `a(r, k) = h(k + 1, r + 1) - h(k, r + 1) - h(k + 1, r) + h(k, r)`.
2. **Row-comparison rhombi** (`0 ≤ x ≤ r` and `r + 2 ≤ n`):
   `h(x, r) + h(x + 1, r + 2) ≤ h(x, r + 1) + h(x + 1, r + 1)` telescopes to column strictness
   `λ_{r + 1} + ∑_{k ≤ x} a(r + 1, k) ≤ λ_r + ∑_{k < x} a(r, k)` when rows are filled weakly
   increasingly via `TauCeti.SkewSemistandardYoungTableau.ofRowCount`.
3. **Ballot rhombi** (`0 ≤ k < x < n`):
   `h(k, x) + h(k + 2, x + 1) ≤ h(k + 1, x) + h(k + 1, x + 1)` telescopes to the Yamanouchi
   lattice-word prefix inequalities `∑_{r ≤ x} a(r, k + 1) ≤ ∑_{r < x} a(r, k)`
   (`TauCeti.SkewSemistandardYoungTableau.isLatticeWord_readingWord_iff`), and along `x = k + 1`
   forces the diagonal counts `a(r, r) = h(r + 1, r + 1) - h(r, r + 1)` to decrease weakly down to
   `a(n - 1, n - 1) = μ_{n - 1}`.

For polynomial dominant weights `λ, μ, γ : DominantWeight n`, the forward sum
`h(i, j) = ∑_{r < j} λ_r + ∑_{k < i} ∑_{k ≤ r < j} a(r, k)` and the inverse difference extraction
assemble into an explicit bijection of objects
`FixedIntegerHive (productBoundary λ μ γ) ≃ LRTableau λ.shape γ.shape μ.shape`
(`TauCeti.Hive.fixedIntegerHiveEquivLRTableau`).

For arbitrary signed dominant weights `λ, μ, γ : DominantWeight n`, adding the zero-slack affine
hive `Hive.affine n a (a + b)` shifts `(λ, μ, γ)` to `(λ.shift a, μ.shift b, γ.shift (a + b))`
(`TauCeti.Hive.fixedIntegerHiveShiftEquiv`). Subtracting `λ.detShift` and `μ.detShift` yields an
explicit bijection with `LRTableau λ.detShiftShape (γ.shift (-(λ.detShift + μ.detShift))).shape
μ.detShiftShape` whenever `λ.detShift + μ.detShift ≤ γ.detShift`
(`TauCeti.Hive.fixedIntegerHiveSignedEquivLRTableau`), while the fibre is empty when
`γ.detShift < λ.detShift + μ.detShift`; any two polynomializing shift pairs induce canonically
equivalent tableau carriers (`TauCeti.Hive.lrTableauShiftEquiv`).

## Main definitions

* `TauCeti.Hive.Vertex.productVertex`: `(i, j)` product-chart parameterization of `Vertex n`.
* `TauCeti.Hive.hiveOfLRTableau` and `TauCeti.Hive.lrTableauOfHive`: explicit mutually inverse
  constructions between Littlewood–Richardson tableaux and normalized integer hives.
* `TauCeti.Hive.fixedIntegerHiveEquivLRTableau` and
  `TauCeti.Hive.fixedIntegerHiveWeightOfShapeEquivLRTableau`: the polynomial and Young-diagram
  hive-to-Littlewood–Richardson equivalences.
* `TauCeti.Hive.fixedIntegerHiveShiftEquiv`, `TauCeti.Hive.fixedIntegerHiveSignedEquivLRTableau`,
  and `TauCeti.Hive.lrTableauShiftEquiv`: affine determinant-shift equivalences for arbitrary
  signed dominant weights.

## Main results

* `TauCeti.Hive.isRhombusConcave_iff_productVertex`: characterization of hive concavity by the
  three product-chart unit-rhombus families.
* `TauCeti.Hive.boundary_hiveOfLRTableau` and `TauCeti.Hive.hiveRowCount_hiveOfLRTableau`:
  boundary and row-count inversion identities for `hiveOfLRTableau`.
* `TauCeti.Hive.hiveCount_productBoundary_shift` and
  `TauCeti.Hive.rowCount_lrTableauShiftEquiv`: determinant-shift covariance of `hiveCount` and
  row-count shift formula across `lrTableauShiftEquiv`.

## References

* A. Knutson and T. Tao, *The honeycomb model of GLₙ(ℂ) tensor products I: Proof of the saturation
  conjecture*, J. Amer. Math. Soc. 12 (1999), 1055–1090, Appendix 2.
* A. S. Buch, *The saturation conjecture (after A. Knutson and T. Tao)*, Enseign. Math. (2) 46
  (2000), 43–60, Theorem 3.18.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

/-! ### The product chart and the three unit-rhombus families -/

namespace Vertex

/-- The `(i, j)` product-chart parameterization `(n - j, j - i, i)` of `Vertex n` for
`0 ≤ i ≤ j ≤ n`. -/
def productVertex (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) : Vertex n :=
  ⟨n - j, j - i, i, by omega⟩

@[simp] theorem productVertex_x (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) :
    (productVertex n i j hij hj).x = n - j := (rfl)

@[simp] theorem productVertex_y (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) :
    (productVertex n i j hij hj).y = j - i := (rfl)

@[simp] theorem productVertex_z (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) :
    (productVertex n i j hij hj).z = i := (rfl)

@[simp] theorem productVertex_eq_iff {n i₁ j₁ i₂ j₂ : ℕ}
    {hij₁ : i₁ ≤ j₁} {hj₁ : j₁ ≤ n} {hij₂ : i₂ ≤ j₂} {hj₂ : j₂ ≤ n} :
    productVertex n i₁ j₁ hij₁ hj₁ = productVertex n i₂ j₂ hij₂ hj₂ ↔ i₁ = i₂ ∧ j₁ = j₂ := by
  refine ⟨fun h => ?_, fun ⟨hi, hj⟩ => by subst hi; subst hj; rfl⟩
  have hy : j₁ - i₁ = j₂ - i₂ := congrArg Vertex.y h
  have hz : i₁ = i₂ := congrArg Vertex.z h
  omega

/-- Every lattice vertex `p : Vertex n` is `productVertex n p.z (p.y + p.z)`. -/
@[simp] theorem productVertex_z_add {n : ℕ} (p : Vertex n) :
    productVertex n p.z (p.y + p.z) (Nat.le_add_left _ _) (by have := p.sum_eq; omega) = p := by
  have := p.sum_eq; ext <;> simp; omega

@[simp] theorem productVertex_zero_zero (n : ℕ) :
    productVertex n 0 0 le_rfl (Nat.zero_le n) = cornerA n := by
  ext <;> simp

/-- Setting `i = 0` gives the `j`-th vertex along side `A → B` (`s = 0`). -/
theorem productVertex_zero_left (n j : ℕ) (hj : j ≤ n) :
    productVertex n 0 j (Nat.zero_le j) hj = edgePoint n 0 ⟨j, by omega⟩ := by
  ext <;> simp

/-- Setting `j = n` gives the `i`-th vertex along side `B → C` (`s = 1`). -/
theorem productVertex_right_self (n i : ℕ) (hi : i ≤ n) :
    productVertex n i n hi le_rfl = edgePoint n 1 ⟨i, by omega⟩ := by
  ext <;> simp

/-- Setting `i = j` gives the `(n - j)`-th vertex along side `C → A` (`s = 2`). -/
theorem productVertex_diag (n j : ℕ) (hj : j ≤ n) :
    productVertex n j j le_rfl hj = edgePoint n 2 ⟨n - j, by omega⟩ := by
  ext <;> simp; omega

end Vertex

/-- First unit-rhombus family in the product chart (`0 ≤ i < j < n`): obtuse corners `(i, j)` and
`(i + 1, j + 1)`, acute corners `(i + 1, j)` and `(i, j + 1)`. -/
theorem isRhombus_productVertex_mixed {n i j : ℕ} (hij : i < j) (hj : j + 1 ≤ n) :
    IsRhombus
      (Vertex.productVertex n i j (by omega) (by omega))
      (Vertex.productVertex n (i + 1) j (by omega) (by omega))
      (Vertex.productVertex n (i + 1) (j + 1) (by omega) hj)
      (Vertex.productVertex n i (j + 1) (by omega) hj) := by
  have hx0 : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
  have hx1 : ((n - (j + 1) : ℕ) : ℤ) = (n : ℤ) - j - 1 := by omega
  have hy00 : ((j - i : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy10 : ((j - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i - 1 := by omega
  have hy11 : ((j + 1 - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy01 : ((j + 1 - i : ℕ) : ℤ) = (j : ℤ) - i + 1 := by omega
  refine ⟨rfl, by simp only [Vertex.productVertex_y]; omega,
    by simp only [Vertex.productVertex_z]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [Vertex.sqDist_def]
    simp only [Vertex.productVertex_x, Vertex.productVertex_y, Vertex.productVertex_z,
      hx0, hx1, hy00, hy10, hy11, hy01, Nat.cast_add, Nat.cast_one]
    ring

/-- Second unit-rhombus family in the product chart (`0 ≤ i ≤ j` and `j + 2 ≤ n`): obtuse corners
`(i, j + 1)` and `(i + 1, j + 1)`, acute corners `(i, j)` and `(i + 1, j + 2)`. -/
theorem isRhombus_productVertex_col {n i j : ℕ} (hij : i ≤ j) (hj : j + 2 ≤ n) :
    IsRhombus
      (Vertex.productVertex n i (j + 1) (by omega) (by omega))
      (Vertex.productVertex n i j hij (by omega))
      (Vertex.productVertex n (i + 1) (j + 1) (by omega) (by omega))
      (Vertex.productVertex n (i + 1) (j + 2) (by omega) hj) := by
  have hx0 : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
  have hx1 : ((n - (j + 1) : ℕ) : ℤ) = (n : ℤ) - j - 1 := by omega
  have hx2 : ((n - (j + 2) : ℕ) : ℤ) = (n : ℤ) - j - 2 := by omega
  have hy00 : ((j - i : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy01 : ((j + 1 - i : ℕ) : ℤ) = (j : ℤ) - i + 1 := by omega
  have hy11 : ((j + 1 - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy12 : ((j + 2 - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i + 1 := by omega
  refine ⟨by simp only [Vertex.productVertex_x]; omega,
    by simp only [Vertex.productVertex_y]; omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [Vertex.sqDist_def]
    simp only [Vertex.productVertex_x, Vertex.productVertex_y, Vertex.productVertex_z,
      hx0, hx1, hx2, hy00, hy01, hy11, hy12, Nat.cast_add, Nat.cast_one]
    ring

/-- Third unit-rhombus family in the product chart (`0 ≤ i < j < n`): obtuse corners `(i + 1, j)`
and `(i + 1, j + 1)`, acute corners `(i, j)` and `(i + 2, j + 1)`. -/
theorem isRhombus_productVertex_ballot {n i j : ℕ} (hij : i < j) (hj : j + 1 ≤ n) :
    IsRhombus
      (Vertex.productVertex n (i + 1) j (by omega) (by omega))
      (Vertex.productVertex n i j (by omega) (by omega))
      (Vertex.productVertex n (i + 1) (j + 1) (by omega) hj)
      (Vertex.productVertex n (i + 2) (j + 1) (by omega) hj) := by
  have hx0 : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
  have hx1 : ((n - (j + 1) : ℕ) : ℤ) = (n : ℤ) - j - 1 := by omega
  have hy00 : ((j - i : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy10 : ((j - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i - 1 := by omega
  have hy11 : ((j + 1 - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy21 : ((j + 1 - (i + 2) : ℕ) : ℤ) = (j : ℤ) - i - 1 := by omega
  refine ⟨rfl, by simp only [Vertex.productVertex_y]; omega,
    by simp only [Vertex.productVertex_z]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [Vertex.sqDist_def]
    simp only [Vertex.productVertex_x, Vertex.productVertex_y, Vertex.productVertex_z,
      hx0, hx1, hy00, hy10, hy11, hy21, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring

private theorem long_diag_cases {n : ℕ} {b d : Vertex n} (hlong : b.sqDist d = 6) :
    (((b.x : ℤ) - d.x = 1 ∧ (b.y : ℤ) - d.y = -2 ∧ (b.z : ℤ) - d.z = 1) ∨
      ((b.x : ℤ) - d.x = -1 ∧ (b.y : ℤ) - d.y = 2 ∧ (b.z : ℤ) - d.z = -1) ∨
      ((b.x : ℤ) - d.x = 2 ∧ (b.y : ℤ) - d.y = -1 ∧ (b.z : ℤ) - d.z = -1) ∨
      ((b.x : ℤ) - d.x = -2 ∧ (b.y : ℤ) - d.y = 1 ∧ (b.z : ℤ) - d.z = 1) ∨
      ((b.x : ℤ) - d.x = 1 ∧ (b.y : ℤ) - d.y = 1 ∧ (b.z : ℤ) - d.z = -2) ∨
      ((b.x : ℤ) - d.x = -1 ∧ (b.y : ℤ) - d.y = -1 ∧ (b.z : ℤ) - d.z = 2)) := by
  have bnd : ∀ a : ℤ, a ^ 2 ≤ 6 → -2 ≤ a ∧ a ≤ 2 := fun a ha => by
    refine ⟨?_, ?_⟩
    · by_contra! h'; have : a ≤ -3 := by omega
      nlinarith
    · by_contra! h'; have : 3 ≤ a := by omega
      nlinarith
  have hbsum := b.sum_eq; have hdsum := d.sum_eq
  rw [Vertex.sqDist_def] at hlong
  set dx : ℤ := (b.x : ℤ) - d.x
  set dy : ℤ := (b.y : ℤ) - d.y
  set dz : ℤ := (b.z : ℤ) - d.z
  have hdx := bnd dx (by linarith [sq_nonneg dy, sq_nonneg dz])
  have hdy := bnd dy (by linarith [sq_nonneg dx, sq_nonneg dz])
  have hdz : dz = -dx - dy := by omega
  rw [hdz] at hlong ⊢
  rcases (by omega : dx = -2 ∨ dx = -1 ∨ dx = 0 ∨ dx = 1 ∨ dx = 2) with
    h1 | h1 | h1 | h1 | h1 <;>
  rcases (by omega : dy = -2 ∨ dy = -1 ∨ dy = 0 ∨ dy = 1 ∨ dy = 2) with
    h2 | h2 | h2 | h2 | h2 <;>
  rw [h1, h2] at hlong ⊢ <;> revert hlong <;> decide

private theorem short_diag_bounds {n : ℕ} {a c : Vertex n} (hshort : a.sqDist c = 2) :
    (-1 ≤ (a.x : ℤ) - c.x ∧ (a.x : ℤ) - c.x ≤ 1) ∧
      (-1 ≤ (a.y : ℤ) - c.y ∧ (a.y : ℤ) - c.y ≤ 1) ∧
      (-1 ≤ (a.z : ℤ) - c.z ∧ (a.z : ℤ) - c.z ≤ 1) := by
  have bnd : ∀ u : ℤ, u ^ 2 ≤ 2 → -1 ≤ u ∧ u ≤ 1 := fun u hu => by
    refine ⟨?_, ?_⟩
    · by_contra! h'; have : u ≤ -2 := by omega
      nlinarith
    · by_contra! h'; have : 2 ≤ u := by omega
      nlinarith
  rw [Vertex.sqDist_def] at hshort
  exact ⟨bnd _ (by linarith [sq_nonneg ((a.y : ℤ) - c.y), sq_nonneg ((a.z : ℤ) - c.z)]),
    bnd _ (by linarith [sq_nonneg ((a.x : ℤ) - c.x), sq_nonneg ((a.z : ℤ) - c.z)]),
    bnd _ (by linarith [sq_nonneg ((a.x : ℤ) - c.x), sq_nonneg ((a.y : ℤ) - c.y)])⟩

private theorem apply_eq_productVertex {n : ℕ} {R : Type*} (f : Vertex n → R) (p : Vertex n)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) (hz : p.z = i) (hyz : p.y + p.z = j) :
    f p = f (Vertex.productVertex n i j hij hj) :=
  congrArg f (by have := p.sum_eq; ext <;> simp <;> omega)

private theorem productVertex_rhombus_le {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]
    {f : Vertex n → R}
    (hmix : ∀ (i j : ℕ) (hij : i < j) (hj : j + 1 ≤ n),
      f (Vertex.productVertex n (i + 1) j (by omega) (by omega)) +
        f (Vertex.productVertex n i (j + 1) (by omega) hj) ≤
      f (Vertex.productVertex n i j (by omega) (by omega)) +
        f (Vertex.productVertex n (i + 1) (j + 1) (by omega) hj))
    (hcol : ∀ (i j : ℕ) (hij : i ≤ j) (hj : j + 2 ≤ n),
      f (Vertex.productVertex n i j hij (by omega)) +
        f (Vertex.productVertex n (i + 1) (j + 2) (by omega) hj) ≤
      f (Vertex.productVertex n i (j + 1) (by omega) (by omega)) +
        f (Vertex.productVertex n (i + 1) (j + 1) (by omega) (by omega)))
    (hbal : ∀ (i j : ℕ) (hij : i < j) (hj : j + 1 ≤ n),
      f (Vertex.productVertex n i j (by omega) (by omega)) +
        f (Vertex.productVertex n (i + 2) (j + 1) (by omega) hj) ≤
      f (Vertex.productVertex n (i + 1) j (by omega) (by omega)) +
        f (Vertex.productVertex n (i + 1) (j + 1) (by omega) hj))
    {a b c d : Vertex n} (hr : IsRhombus a b c d)
    (hor : ((b.x : ℤ) - d.x = 1 ∧ (b.y : ℤ) - d.y = -2 ∧ (b.z : ℤ) - d.z = 1) ∨
      ((b.x : ℤ) - d.x = 2 ∧ (b.y : ℤ) - d.y = -1 ∧ (b.z : ℤ) - d.z = -1) ∨
      ((b.x : ℤ) - d.x = 1 ∧ (b.y : ℤ) - d.y = 1 ∧ (b.z : ℤ) - d.z = -2)) :
    f b + f d ≤ f a + f c := by
  suffices hnorm : ∀ {u v : Vertex n}, IsRhombus u b v d →
      (u.z < v.z ∨ (u.z = v.z ∧ v.x ≤ u.x)) → f b + f d ≤ f u + f v by
    rcases lt_trichotomy a.z c.z with hlt | heq | hgt
    · exact hnorm hr (Or.inl hlt)
    · rcases le_total c.x a.x with hx | hx
      · exact hnorm hr (Or.inr ⟨heq, hx⟩)
      · rw [add_comm (f a)]; exact hnorm hr.swap_opposite.reverse (Or.inr ⟨heq.symm, hx⟩)
    · rw [add_comm (f a)]; exact hnorm hr.swap_opposite.reverse (Or.inl hgt)
  intro u v hruv huv
  have hu := u.sum_eq; have hv := v.sum_eq; have hb := b.sum_eq; have hd := d.sum_eq
  have hmx := hruv.midpoint_x; have hmy := hruv.midpoint_y
  obtain ⟨hux, huy, huz⟩ := short_diag_bounds hruv.short
  rcases hor with ⟨hdx, hdy, -⟩ | ⟨hdx, hdy, -⟩ | ⟨hdx, hdy, -⟩
  · rw [apply_eq_productVertex f b (d.z + 1) (b.y + 1 + d.z) (by omega) (by omega)
        (by omega) (by omega),
      apply_eq_productVertex f d d.z (b.y + 1 + d.z + 1) (by omega) (by omega) rfl (by omega),
      apply_eq_productVertex f u d.z (b.y + 1 + d.z) (by omega) (by omega) (by omega) (by omega),
      apply_eq_productVertex f v (d.z + 1) (b.y + 1 + d.z + 1) (by omega) (by omega)
        (by omega) (by omega)]
    exact hmix d.z (b.y + 1 + d.z) (by omega) (by omega)
  · rw [apply_eq_productVertex f b b.z (b.y + b.z) (by omega) (by omega) rfl rfl,
      apply_eq_productVertex f d (b.z + 1) (b.y + b.z + 2) (by omega) (by omega)
        (by omega) (by omega),
      apply_eq_productVertex f u b.z (b.y + b.z + 1) (by omega) (by omega) (by omega) (by omega),
      apply_eq_productVertex f v (b.z + 1) (b.y + b.z + 1) (by omega) (by omega)
        (by omega) (by omega)]
    exact hcol b.z (b.y + b.z) (by omega) (by omega)
  · rw [apply_eq_productVertex f b b.z (d.y + 1 + b.z) (by omega) (by omega) rfl (by omega),
      apply_eq_productVertex f d (b.z + 2) (d.y + 1 + b.z + 1) (by omega) (by omega)
        (by omega) (by omega),
      apply_eq_productVertex f u (b.z + 1) (d.y + 1 + b.z) (by omega) (by omega)
        (by omega) (by omega),
      apply_eq_productVertex f v (b.z + 1) (d.y + 1 + b.z + 1) (by omega) (by omega)
        (by omega) (by omega)]
    exact hbal b.z (d.y + 1 + b.z) (by omega) (by omega)

/-- **Product-chart characterization of hive concavity**: `f : Vertex n → R` is rhombus-concave iff
it satisfies the three product-chart rhombus inequality families (mixed differences, row
comparison, and ballot prefixes). -/
theorem isRhombusConcave_iff_productVertex {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]
    (f : Vertex n → R) :
    IsRhombusConcave f ↔
      (∀ (i j : ℕ) (hij : i < j) (hj : j + 1 ≤ n),
        f (Vertex.productVertex n (i + 1) j (by omega) (by omega)) +
          f (Vertex.productVertex n i (j + 1) (by omega) hj) ≤
        f (Vertex.productVertex n i j (by omega) (by omega)) +
          f (Vertex.productVertex n (i + 1) (j + 1) (by omega) hj)) ∧
      (∀ (i j : ℕ) (hij : i ≤ j) (hj : j + 2 ≤ n),
        f (Vertex.productVertex n i j hij (by omega)) +
          f (Vertex.productVertex n (i + 1) (j + 2) (by omega) hj) ≤
        f (Vertex.productVertex n i (j + 1) (by omega) (by omega)) +
          f (Vertex.productVertex n (i + 1) (j + 1) (by omega) (by omega))) ∧
      (∀ (i j : ℕ) (hij : i < j) (hj : j + 1 ≤ n),
        f (Vertex.productVertex n i j (by omega) (by omega)) +
          f (Vertex.productVertex n (i + 2) (j + 1) (by omega) hj) ≤
        f (Vertex.productVertex n (i + 1) j (by omega) (by omega)) +
          f (Vertex.productVertex n (i + 1) (j + 1) (by omega) hj)) := by
  rw [isRhombusConcave_def]
  refine ⟨fun hf => ⟨fun i j hij hj => hf (isRhombus_productVertex_mixed hij hj),
      fun i j hij hj => hf (isRhombus_productVertex_col hij hj),
      fun i j hij hj => hf (isRhombus_productVertex_ballot hij hj)⟩, ?_⟩
  rintro ⟨hmix, hcol, hbal⟩ a b c d hr
  rcases long_diag_cases hr.long with h1 | h1 | h2 | h2 | h3 | h3
  · exact productVertex_rhombus_le hmix hcol hbal hr (Or.inl h1)
  · rw [add_comm (f b)]
    exact productVertex_rhombus_le hmix hcol hbal hr.reverse (Or.inl (by omega))
  · exact productVertex_rhombus_le hmix hcol hbal hr (Or.inr (Or.inl h2))
  · rw [add_comm (f b)]
    exact productVertex_rhombus_le hmix hcol hbal hr.reverse (Or.inr (Or.inl (by omega)))
  · exact productVertex_rhombus_le hmix hcol hbal hr (Or.inr (Or.inr h3))
  · rw [add_comm (f b)]
    exact productVertex_rhombus_le hmix hcol hbal hr.reverse (Or.inr (Or.inr (by omega)))

/-! ### Forward map: from a Littlewood–Richardson tableau to an integer hive -/

section ForwardMap

private theorem filter_lt_succ_sum {n : ℕ} (l : DominantWeight n) {j : ℕ} (hj : j < n) :
    (∑ r : Fin n with r.val < j + 1, l.1 r) =
      (∑ r : Fin n with r.val < j, l.1 r) + l.1 ⟨j, hj⟩ := by
  have hset : ({r : Fin n | r.val < j + 1} : Finset (Fin n)) =
      insert ⟨j, hj⟩ ({r : Fin n | r.val < j} : Finset (Fin n)) := by
    ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hmem : (⟨j, hj⟩ : Fin n) ∉ ({r : Fin n | r.val < j} : Finset (Fin n)) := by simp
  rw [hset, Finset.sum_insert hmem, add_comm]

private theorem sum_filter_lt_eq_sum_range_rowLen {n : ℕ} {l : DominantWeight n}
    (hl : l.IsPolynomial) {j : ℕ} (hj : j ≤ n) :
    (∑ r : Fin n with r.val < j, l.1 r) = ∑ r ∈ Finset.range j, (l.shape.rowLen r : ℤ) := by
  induction j with
  | zero => simp
  | succ m ih =>
    rw [filter_lt_succ_sum l (by omega), Finset.sum_range_succ, ih (by omega),
      DominantWeight.natCast_rowLen_shape hl ⟨m, by omega⟩]

/-- The lattice function on `Vertex n` attached to a dominant weight `λ` and a skew tableau `T`:
at `productVertex n i j` it sums `λ_r` for `r < j` plus the counts of letters `k < i` in rows
`r < j`. -/
def lrHiveFun {n : ℕ} {inner outer : YoungDiagram} (lam : DominantWeight n)
    (T : SkewSemistandardYoungTableau inner outer) (p : Vertex n) : ℤ :=
  (∑ r : Fin n with r.val < p.y + p.z, lam.1 r) +
    ∑ k ∈ Finset.range p.z, ∑ r ∈ Finset.range (p.y + p.z), (T.rowCount r k : ℤ)

theorem lrHiveFun_apply {n : ℕ} {inner outer : YoungDiagram} (lam : DominantWeight n)
    (T : SkewSemistandardYoungTableau inner outer) (p : Vertex n) :
    lrHiveFun lam T p =
      (∑ r : Fin n with r.val < p.y + p.z, lam.1 r) +
        ∑ k ∈ Finset.range p.z, ∑ r ∈ Finset.range (p.y + p.z), (T.rowCount r k : ℤ) := (rfl)

@[simp] theorem lrHiveFun_cornerA {n : ℕ} {inner outer : YoungDiagram} (lam : DominantWeight n)
    (T : SkewSemistandardYoungTableau inner outer) :
    lrHiveFun lam T (Vertex.cornerA n) = 0 := by
  simp [lrHiveFun]

@[simp] theorem lrHiveFun_productVertex {n i j : ℕ} {inner outer : YoungDiagram}
    (lam : DominantWeight n) (T : SkewSemistandardYoungTableau inner outer)
    (hij : i ≤ j) (hj : j ≤ n) :
    lrHiveFun lam T (Vertex.productVertex n i j hij hj) =
      (∑ r : Fin n with r.val < j, lam.1 r) +
        ∑ k ∈ Finset.range i, ∑ r ∈ Finset.range j, (T.rowCount r k : ℤ) := by
  have hyz : j - i + i = j := by omega
  simp [lrHiveFun, hyz]

/-- For a Littlewood–Richardson tableau `T`, letter `k` never appears above row `k`
(`T.1.rowCount r k = 0` for `r < k`). -/
theorem rowCount_eq_zero_of_lt {inner outer μ : YoungDiagram} (T : LRTableau inner outer μ)
    {r k : ℕ} (hrk : r < k) : T.1.rowCount r k = 0 := by
  rw [SkewSemistandardYoungTableau.rowCount_def, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c _ hc
  have hle := T.entry_le r c
  omega

/-- On a Littlewood–Richardson tableau, `lrHiveFun` restricts the inner row sum to `k ≤ r < j`:
`h(i, j) = ∑_{r < j} λ_r + ∑_{k < i} ∑_{k ≤ r < j} T.rowCount r k`. -/
theorem lrHiveFun_productVertex_eq_sum_Ico {n i j : ℕ} {inner outer μ : YoungDiagram}
    (lam : DominantWeight n) (T : LRTableau inner outer μ) (hij : i ≤ j) (hj : j ≤ n) :
    lrHiveFun lam T.1 (Vertex.productVertex n i j hij hj) =
      (∑ r : Fin n with r.val < j, lam.1 r) +
        ∑ k ∈ Finset.range i, ∑ r ∈ Finset.Ico k j, (T.1.rowCount r k : ℤ) := by
  rw [lrHiveFun_productVertex]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkj : k ≤ j := (Finset.mem_range.mp hk).le.trans hij
  rw [← Finset.sum_range_add_sum_Ico _ hkj,
    Finset.sum_eq_zero fun r hr => by simp [rowCount_eq_zero_of_lt T (Finset.mem_range.mp hr)],
    zero_add]

/-- Forward construction of an `IntegerHive n` from a polynomial dominant weight `λ` and a
Littlewood–Richardson tableau `T : LRTableau λ.shape outer μ`. -/
def hiveOfLRTableau {n : ℕ} {outer μ : YoungDiagram} {lam : DominantWeight n}
    (hlam : lam.IsPolynomial) (T : LRTableau lam.shape outer μ) : IntegerHive n where
  value := lrHiveFun lam T.1
  value_cornerA' := lrHiveFun_cornerA lam T.1
  le_of_isRhombus' {a b c d} hr := by
    refine (isRhombusConcave_def _).mp
      ((isRhombusConcave_iff_productVertex (lrHiveFun lam T.1)).mpr ⟨?_, ?_, ?_⟩) hr
    · intro i j hij hj
      simp only [lrHiveFun_productVertex, filter_lt_succ_sum lam (by omega : j < n),
        Finset.sum_range_succ]
      linarith [Nat.cast_nonneg (α := ℤ) (T.1.rowCount j i)]
    · intro i j hij hj
      have hj1 : j < n := by omega
      have hj2 : j + 1 < n := by omega
      simp only [lrHiveFun_productVertex, filter_lt_succ_sum lam hj1,
        filter_lt_succ_sum lam hj2]
      have hlam_j : lam.1 ⟨j, hj1⟩ = (lam.shape.rowLen j : ℤ) :=
        (DominantWeight.natCast_rowLen_shape hlam ⟨j, hj1⟩).symm
      have hlam_j1 : lam.1 ⟨j + 1, hj2⟩ = (lam.shape.rowLen (j + 1) : ℤ) :=
        (DominantWeight.natCast_rowLen_shape hlam ⟨j + 1, hj2⟩).symm
      have hcol : (lam.shape.rowLen (j + 1) : ℤ) +
          ∑ k ∈ Finset.range (i + 1), (T.1.rowCount (j + 1) k : ℤ) ≤
          (lam.shape.rowLen j : ℤ) + ∑ k ∈ Finset.range i, (T.1.rowCount j k : ℤ) := by
        exact_mod_cast T.1.rowLen_add_sum_range_rowCount_succ_le j i
      have hdiff1 :
          (∑ k ∈ Finset.range i, ∑ r ∈ Finset.range (j + 1), (T.1.rowCount r k : ℤ)) -
            (∑ k ∈ Finset.range i, ∑ r ∈ Finset.range j, (T.1.rowCount r k : ℤ)) =
          ∑ k ∈ Finset.range i, (T.1.rowCount j k : ℤ) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_range_succ]; abel
      have hdiff2 :
          (∑ k ∈ Finset.range (i + 1), ∑ r ∈ Finset.range (j + 2), (T.1.rowCount r k : ℤ)) -
            (∑ k ∈ Finset.range (i + 1), ∑ r ∈ Finset.range (j + 1), (T.1.rowCount r k : ℤ)) =
          ∑ k ∈ Finset.range (i + 1), (T.1.rowCount (j + 1) k : ℤ) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_range_succ]; abel
      linarith
    · intro i j hij hj
      simp only [lrHiveFun_productVertex, Finset.sum_range_succ (n := i + 1),
        Finset.sum_range_succ (n := i)]
      have hlat : ∑ r ∈ Finset.range (j + 1), (T.1.rowCount r (i + 1) : ℤ) ≤
          ∑ r ∈ Finset.range j, (T.1.rowCount r i : ℤ) := by
        exact_mod_cast (T.1.isLatticeWord_readingWord_iff.mp T.2.2) i j
      linarith

@[simp] theorem hiveOfLRTableau_apply {n : ℕ} {outer μ : YoungDiagram} {lam : DominantWeight n}
    (hlam : lam.IsPolynomial) (T : LRTableau lam.shape outer μ) (p : Vertex n) :
    hiveOfLRTableau hlam T p = lrHiveFun lam T.1 p := (rfl)

theorem hiveOfLRTableau_productVertex {n i j : ℕ} {outer μ : YoungDiagram}
    {lam : DominantWeight n} (hlam : lam.IsPolynomial) (T : LRTableau lam.shape outer μ)
    (hij : i ≤ j) (hj : j ≤ n) :
    hiveOfLRTableau hlam T (Vertex.productVertex n i j hij hj) =
      (∑ r : Fin n with r.val < j, lam.1 r) +
        ∑ k ∈ Finset.range i, ∑ r ∈ Finset.range j, (T.1.rowCount r k : ℤ) :=
  lrHiveFun_productVertex lam T.1 hij hj

/-- Along the diagonal `i = j`, `hiveOfLRTableau` records the prefix sums of `γ`. -/
theorem hiveOfLRTableau_productVertex_diag {n j : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) (hj : j ≤ n) :
    hiveOfLRTableau hlam T (Vertex.productVertex n j j le_rfl hj) =
      ∑ r : Fin n with r.val < j, γ.1 r := by
  rw [hiveOfLRTableau_productVertex, sum_filter_lt_eq_sum_range_rowLen hlam hj,
    sum_filter_lt_eq_sum_range_rowLen hγ hj, Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrj : r < j := Finset.mem_range.mp hr
  have hsum_nat : ∑ k ∈ Finset.range j, T.1.rowCount r k =
      γ.shape.rowLen r - lam.shape.rowLen r :=
    T.1.sum_range_rowCount_of_forall_lt fun c _ _ => (T.entry_le r c).trans_lt hrj
  have hle_row : lam.shape.rowLen r ≤ γ.shape.rowLen r :=
    YoungDiagram.rowLen_le_of_le T.1.le r
  rw [← Nat.cast_sum, hsum_nat]
  omega

/-- The clockwise cyclic boundary of `hiveOfLRTableau hlam T` is `productBoundary lam μ γ`. -/
@[simp] theorem boundary_hiveOfLRTableau {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) :
    (hiveOfLRTableau hlam T).boundary = productBoundary lam μ γ := by
  ext s m
  rw [boundary_apply]
  fin_cases s
  · dsimp only; simp only [Fin.zero_eta]
    have hsucc : Vertex.edgePoint n 0 m.succ =
        Vertex.productVertex n 0 (m.val + 1) (Nat.zero_le _) (by omega) :=
      (Vertex.productVertex_zero_left n (m.val + 1) (by omega)).symm
    have hcast : Vertex.edgePoint n 0 m.castSucc =
        Vertex.productVertex n 0 m.val (Nat.zero_le _) (by omega) :=
      (Vertex.productVertex_zero_left n m.val (by omega)).symm
    rw [hsucc, hcast, hiveOfLRTableau_productVertex, hiveOfLRTableau_productVertex,
      filter_lt_succ_sum lam m.isLt]
    simp
  · dsimp only; simp only [Fin.mk_one]
    have hsucc : Vertex.edgePoint n 1 m.succ =
        Vertex.productVertex n (m.val + 1) n (by omega) le_rfl :=
      (Vertex.productVertex_right_self n (m.val + 1) (by omega)).symm
    have hcast : Vertex.edgePoint n 1 m.castSucc =
        Vertex.productVertex n m.val n (by omega) le_rfl :=
      (Vertex.productVertex_right_self n m.val (by omega)).symm
    rw [hsucc, hcast, hiveOfLRTableau_productVertex, hiveOfLRTableau_productVertex,
      Finset.sum_range_succ]
    have hcont : ∑ r ∈ Finset.range n, T.1.rowCount r m.val = μ.shape.rowLen m.val := by
      rw [T.1.sum_range_rowCount_eq_content m.val (DominantWeight.colLen_zero_shape_le γ),
        congrFun T.2.1 m.val]
    have hμ_m : (μ.shape.rowLen m.val : ℤ) = μ.1 m := DominantWeight.natCast_rowLen_shape hμ m
    rw [← Nat.cast_sum, hcont, hμ_m]
    simp only [productBoundary_one]
    abel
  · dsimp only; simp only [Fin.reduceFinMk]
    have hsucc : Vertex.edgePoint n 2 m.succ =
        Vertex.productVertex n (n - (m.val + 1)) (n - (m.val + 1)) le_rfl (by omega) := by
      rw [Vertex.productVertex_diag]
      congr 1; ext; simp; omega
    have hcast : Vertex.edgePoint n 2 m.castSucc =
        Vertex.productVertex n ((n - (m.val + 1)) + 1) ((n - (m.val + 1)) + 1)
          le_rfl (by omega) := by
      rw [Vertex.productVertex_diag]
      congr 1; ext; simp; omega
    rw [hsucc, hcast, hiveOfLRTableau_productVertex_diag hlam hγ T,
      hiveOfLRTableau_productVertex_diag hlam hγ T,
      filter_lt_succ_sum γ (by omega : n - (m.val + 1) < n)]
    have hrev : (⟨n - (m.val + 1), by omega⟩ : Fin n) = m.rev := by ext; simp [Fin.val_rev]
    rw [hrev]
    simp only [productBoundary_two, DominantWeight.dual_apply]
    abel

/-- Bundled forward map into `FixedIntegerHive (productBoundary lam μ γ)`. -/
def fixedIntegerHiveOfLRTableau {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) :
    FixedIntegerHive (productBoundary lam μ γ) :=
  ⟨hiveOfLRTableau hlam T, boundary_hiveOfLRTableau hlam hμ hγ T⟩

@[simp] theorem coe_fixedIntegerHiveOfLRTableau {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) :
    (fixedIntegerHiveOfLRTableau hlam hμ hγ T).1 = hiveOfLRTableau hlam T := (rfl)

end ForwardMap

/-! ### Inverse map: row-count extraction and tableau reconstruction from a hive -/

section InverseMap

/-- Boundary evaluation along `i = 0` for a hive with boundary `productBoundary lam μ γ`. -/
theorem apply_productVertex_zero_left_of_productBoundary {n j : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) (hj : j ≤ n) :
    h (Vertex.productVertex n 0 j (Nat.zero_le j) hj) = ∑ r : Fin n with r.val < j, lam.1 r := by
  rw [Vertex.productVertex_zero_left, apply_edgePoint_zero, hb, productBoundary_zero]

/-- Boundary evaluation along `j = n` for a hive with boundary `productBoundary lam μ γ`. -/
theorem apply_productVertex_right_self_of_productBoundary {n i : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) (hi : i ≤ n) :
    h (Vertex.productVertex n i n hi le_rfl) =
      (∑ r : Fin n, lam.1 r) + ∑ k : Fin n with k.val < i, μ.1 k := by
  rw [Vertex.productVertex_right_self, apply_edgePoint_one, hb, productBoundary_zero,
    productBoundary_one]

/-- Boundary evaluation along the diagonal `i = j` for a hive with boundary
`productBoundary lam μ γ`. -/
theorem apply_productVertex_diag_of_productBoundary {n j : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) (hj : j ≤ n) :
    h (Vertex.productVertex n j j le_rfl hj) = ∑ r : Fin n with r.val < j, γ.1 r := by
  rw [Vertex.productVertex_diag, apply_edgePoint_two, hb, productBoundary_two]
  simp only [DominantWeight.dual_apply, Finset.sum_neg_distrib, neg_neg, Finset.sum_filter]
  refine (Equiv.sum_comp Fin.revPerm
    (fun m : Fin n => if n - j ≤ m.val then γ.1 m.rev else 0)).symm.trans ?_
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  by_cases hr : r.val < j
  · have hle : n - j ≤ n - (r.val + 1) := by omega
    simp [hr, hle]
  · have hlt : ¬ n - j ≤ n - (r.val + 1) := by omega
    simp [hr, hlt]

/-- Signed row-letter count extracted from a hive `h` at skew row `r` and letter `k`:
the mixed second difference off the diagonal (`k < r < n`), the single horizontal step on the
diagonal (`k = r < n`), and `0` elsewhere. -/
def hiveRowCountInt {n : ℕ} (h : Hive n ℤ) (r k : ℕ) : ℤ :=
  if hr : r < n then
    if hkr : k < r then
      h (Vertex.productVertex n (k + 1) (r + 1) (by omega) (by omega)) -
        h (Vertex.productVertex n k (r + 1) (by omega) (by omega)) -
        h (Vertex.productVertex n (k + 1) r (by omega) (by omega)) +
        h (Vertex.productVertex n k r (by omega) (by omega))
    else if k = r then
      h (Vertex.productVertex n (r + 1) (r + 1) le_rfl (by omega)) -
        h (Vertex.productVertex n r (r + 1) (by omega) (by omega))
    else 0
  else 0

theorem hiveRowCountInt_of_lt {n r k : ℕ} (h : Hive n ℤ) (hkr : k < r) (hr : r < n) :
    hiveRowCountInt h r k =
      h (Vertex.productVertex n (k + 1) (r + 1) (by omega) (by omega)) -
        h (Vertex.productVertex n k (r + 1) (by omega) (by omega)) -
        h (Vertex.productVertex n (k + 1) r (by omega) (by omega)) +
        h (Vertex.productVertex n k r (by omega) (by omega)) := by
  simp [hiveRowCountInt, hr, hkr]

theorem hiveRowCountInt_diag {n r : ℕ} (h : Hive n ℤ) (hr : r < n) :
    hiveRowCountInt h r r =
      h (Vertex.productVertex n (r + 1) (r + 1) le_rfl (by omega)) -
        h (Vertex.productVertex n r (r + 1) (by omega) (by omega)) := by
  simp [hiveRowCountInt, hr]

theorem hiveRowCountInt_eq_zero_of_lt {n r k : ℕ} (h : Hive n ℤ) (hrk : r < k) :
    hiveRowCountInt h r k = 0 := by
  by_cases hr : r < n
  · have h1 : ¬ k < r := by omega
    have h2 : k ≠ r := by omega
    simp [hiveRowCountInt, hr, h1, h2]
  · simp [hiveRowCountInt, hr]

theorem hiveRowCountInt_eq_zero_of_le {n r k : ℕ} (h : Hive n ℤ) (hnr : n ≤ r) :
    hiveRowCountInt h r k = 0 := by
  have hr : ¬ r < n := by omega
  simp [hiveRowCountInt, hr]

/-- **Column telescoping of `hiveRowCountInt`**: summing letter `k` across rows `r < x` (`x ≤ n`)
gives `h(k + 1, x) - h(k, x)` when `k < x`, and `0` when `x ≤ k`. -/
theorem sum_range_hiveRowCountInt_left {n x : ℕ} (h : Hive n ℤ) (k : ℕ) (hx : x ≤ n) :
    ∑ r ∈ Finset.range x, hiveRowCountInt h r k =
      if hkx : k < x then
        h (Vertex.productVertex n (k + 1) x hkx hx) -
          h (Vertex.productVertex n k x (Nat.le_of_lt hkx) hx)
      else 0 := by
  induction x with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    rcases lt_trichotomy k m with hkm | rfl | hmk
    · have hkm' : k < m + 1 := by omega
      rw [dite_eq_left hkm, dite_eq_left hkm', hiveRowCountInt_of_lt h hkm (by omega)]
      abel
    · rw [dite_eq_right (Nat.lt_irrefl k), dite_eq_left (Nat.lt_succ_self k), zero_add,
        hiveRowCountInt_diag h (by omega)]
    · have hnm : ¬ k < m := by omega
      have hnm' : ¬ k < m + 1 := by omega
      rw [dite_eq_right hnm, dite_eq_right hnm', hiveRowCountInt_eq_zero_of_lt h hmk, add_zero]

/-- **Double telescoping of `hiveRowCountInt`**: summing `hiveRowCountInt h r k` over `k < i` and
`r < j` (`0 ≤ i ≤ j ≤ n`) recovers `h(i, j) - h(0, j)`. -/
theorem sum_range_sum_range_hiveRowCountInt {n i j : ℕ} (h : Hive n ℤ)
    (hij : i ≤ j) (hj : j ≤ n) :
    ∑ k ∈ Finset.range i, ∑ r ∈ Finset.range j, hiveRowCountInt h r k =
      h (Vertex.productVertex n i j hij hj) -
        h (Vertex.productVertex n 0 j (Nat.zero_le j) hj) := by
  induction i with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega), sum_range_hiveRowCountInt_left h m hj,
      dite_eq_left (by omega : m < j)]
    abel

/-- Row-prefix telescoping for `i ≤ r < n`. -/
theorem sum_range_hiveRowCountInt_right {n i r : ℕ} (h : Hive n ℤ) (hir : i ≤ r) (hr : r < n) :
    ∑ k ∈ Finset.range i, hiveRowCountInt h r k =
      (h (Vertex.productVertex n i (r + 1) (by omega) (by omega)) -
          h (Vertex.productVertex n i r hir (by omega))) -
        (h (Vertex.productVertex n 0 (r + 1) (Nat.zero_le _) (by omega)) -
          h (Vertex.productVertex n 0 r (Nat.zero_le _) (by omega))) := by
  have h1 := sum_range_sum_range_hiveRowCountInt h (i := i) (j := r + 1) (by omega) (by omega)
  have h2 := sum_range_sum_range_hiveRowCountInt h (i := i) (j := r) hir (by omega)
  have hdiff :
      (∑ k ∈ Finset.range i, ∑ s ∈ Finset.range (r + 1), hiveRowCountInt h s k) -
        (∑ k ∈ Finset.range i, ∑ s ∈ Finset.range r, hiveRowCountInt h s k) =
      ∑ k ∈ Finset.range i, hiveRowCountInt h r k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_range_succ]; abel
  linarith

/-- Full-row telescoping across `k < m` (`r + 1 ≤ m`) for `r < n`. -/
theorem sum_range_hiveRowCountInt_full {n r m : ℕ} (h : Hive n ℤ) (hr : r < n) (hrm : r + 1 ≤ m) :
    ∑ k ∈ Finset.range m, hiveRowCountInt h r k =
      (h (Vertex.productVertex n (r + 1) (r + 1) le_rfl (by omega)) -
          h (Vertex.productVertex n r r le_rfl (by omega))) -
        (h (Vertex.productVertex n 0 (r + 1) (Nat.zero_le _) (by omega)) -
          h (Vertex.productVertex n 0 r (Nat.zero_le _) (by omega))) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrm
  have htail : ∑ x ∈ Finset.range d, hiveRowCountInt h r (r + 1 + x) = 0 :=
    Finset.sum_eq_zero fun x _ => hiveRowCountInt_eq_zero_of_lt h (by omega)
  rw [Finset.sum_range_add, htail, add_zero, Finset.sum_range_succ,
    sum_range_hiveRowCountInt_right h le_rfl hr, hiveRowCountInt_diag h hr]
  abel

/-- On any integer hive, the diagonal counts `hiveRowCountInt h r r` decrease weakly in `r < n`. -/
theorem hiveRowCountInt_diag_antitone {n r₁ r₂ : ℕ} (h : Hive n ℤ)
    (hr₁₂ : r₁ ≤ r₂) (hr₂ : r₂ < n) :
    hiveRowCountInt h r₂ r₂ ≤ hiveRowCountInt h r₁ r₁ := by
  induction r₂, hr₁₂ using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih =>
    refine le_trans ?_ (ih (by omega))
    have hbal := h.le_of_isRhombus
      (isRhombus_productVertex_ballot (n := n) (i := m) (j := m + 1) (Nat.lt_succ_self m)
        (by omega))
    rw [hiveRowCountInt_diag h hr₂, hiveRowCountInt_diag h (by omega)]
    linarith

/-- **Nonnegativity of all extracted counts (including the diagonal)** when `μ` is polynomial. -/
theorem hiveRowCountInt_nonneg {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hμ : μ.IsPolynomial) (r k : ℕ) :
    0 ≤ hiveRowCountInt h r k := by
  by_cases hr : r < n
  · rcases lt_trichotomy k r with hkr | rfl | hrk
    · have hmix := h.le_of_isRhombus (isRhombus_productVertex_mixed hkr (by omega))
      rw [hiveRowCountInt_of_lt h hkr hr]
      linarith
    · have hn : 0 < n := by omega
      refine le_trans ?_ (hiveRowCountInt_diag_antitone h (r₁ := k) (r₂ := n - 1)
        (by omega) (by omega))
      rw [hiveRowCountInt_diag h (by omega : n - 1 < n)]
      have hdiag : h (Vertex.productVertex n (n - 1 + 1) (n - 1 + 1) le_rfl (by omega)) =
          (∑ i, lam.1 i) + ∑ i, μ.1 i := by
        have hv : Vertex.productVertex n (n - 1 + 1) (n - 1 + 1) le_rfl (by omega) =
            Vertex.productVertex n n n le_rfl le_rfl := by ext <;> simp <;> omega
        have huniv : ({i : Fin n | i.val < n} : Finset (Fin n)) = Finset.univ := by ext i; simp
        rw [hv, apply_productVertex_diag_of_productBoundary hb le_rfl, huniv,
          ← sum_eq_of_productBoundary hb]
      have hside : h (Vertex.productVertex n (n - 1) (n - 1 + 1) (by omega) (by omega)) =
          (∑ i, lam.1 i) + ∑ i : Fin n with i.val < n - 1, μ.1 i := by
        have hv : Vertex.productVertex n (n - 1) (n - 1 + 1) (by omega) (by omega) =
            Vertex.productVertex n (n - 1) n (by omega) le_rfl := by ext <;> simp <;> omega
        rw [hv, apply_productVertex_right_self_of_productBoundary hb (by omega)]
      have hsum_μ : ∑ i : Fin n, μ.1 i =
          (∑ i : Fin n with i.val < n - 1, μ.1 i) + μ.1 ⟨n - 1, by omega⟩ := by
        have hall : ({i : Fin n | i.val < n - 1 + 1} : Finset (Fin n)) = Finset.univ := by
          ext i; simp; omega
        have hstep := filter_lt_succ_sum μ (by omega : n - 1 < n)
        rwa [hall] at hstep
      have hμ_nn : 0 ≤ μ.1 ⟨n - 1, by omega⟩ :=
        (DominantWeight.isPolynomial_def μ).mp hμ ⟨n - 1, by omega⟩
      linarith
    · rw [hiveRowCountInt_eq_zero_of_lt h hrk]
  · rw [hiveRowCountInt_eq_zero_of_le h (Nat.le_of_not_lt hr)]

/-- Natural-number row-letter count `a(r, k)` extracted from an integer hive `h`. -/
def hiveRowCount {n : ℕ} (h : IntegerHive n) (r k : ℕ) : ℕ :=
  (hiveRowCountInt h r k).toNat

theorem hiveRowCount_def {n : ℕ} (h : IntegerHive n) (r k : ℕ) :
    hiveRowCount h r k = (hiveRowCountInt h r k).toNat := (rfl)

theorem natCast_hiveRowCount {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hμ : μ.IsPolynomial) (r k : ℕ) :
    (hiveRowCount h r k : ℤ) = hiveRowCountInt h r k :=
  Int.toNat_of_nonneg (hiveRowCountInt_nonneg hb hμ r k)

theorem hiveRowCount_eq_zero_of_lt {n r k : ℕ} (h : IntegerHive n) (hrk : r < k) :
    hiveRowCount h r k = 0 := by
  simp [hiveRowCount, hiveRowCountInt_eq_zero_of_lt h hrk]

theorem hiveRowCount_eq_zero_of_le {n r k : ℕ} (h : IntegerHive n) (hnr : n ≤ r) :
    hiveRowCount h r k = 0 := by
  simp [hiveRowCount, hiveRowCountInt_eq_zero_of_le h hnr]

/-- Extracting `hiveRowCount` from `hiveOfLRTableau hlam T` recovers `T.1.rowCount` whenever
`outer.colLen 0 ≤ n`. -/
@[simp] theorem hiveRowCount_hiveOfLRTableau {n : ℕ} {outer μ : YoungDiagram}
    {lam : DominantWeight n} (hlam : lam.IsPolynomial) (houter : outer.colLen 0 ≤ n)
    (T : LRTableau lam.shape outer μ) (r k : ℕ) :
    hiveRowCount (hiveOfLRTableau hlam T) r k = T.1.rowCount r k := by
  by_cases hr : r < n
  · rcases lt_trichotomy k r with hkr | rfl | hrk
    · have hval : hiveRowCountInt (hiveOfLRTableau hlam T) r k = (T.1.rowCount r k : ℤ) := by
        rw [hiveRowCountInt_of_lt _ hkr hr]
        simp only [hiveOfLRTableau_productVertex, filter_lt_succ_sum lam hr,
          Finset.sum_range_succ]
        abel
      rw [hiveRowCount, hval, Int.toNat_natCast]
    · have hval : hiveRowCountInt (hiveOfLRTableau hlam T) k k = (T.1.rowCount k k : ℤ) := by
        rw [hiveRowCountInt_diag _ hr]
        simp only [hiveOfLRTableau_productVertex, Finset.sum_range_succ (n := k)]
        have hzero : ∑ s ∈ Finset.range k, (T.1.rowCount s k : ℤ) = 0 :=
          Finset.sum_eq_zero fun s hs => by simp [rowCount_eq_zero_of_lt T (Finset.mem_range.mp hs)]
        linarith
      rw [hiveRowCount, hval, Int.toNat_natCast]
    · rw [hiveRowCount_eq_zero_of_lt _ hrk, rowCount_eq_zero_of_lt T hrk]
  · have hnr : n ≤ r := Nat.le_of_not_lt hr
    rw [hiveRowCount_eq_zero_of_le _ hnr]
    have hlen : outer.rowLen r = 0 := YoungDiagram.rowLen_eq_zero_of_colLen_le (houter.trans hnr)
    simp [SkewSemistandardYoungTableau.rowCount_def, hlen]

private theorem shape_le_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ)
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial) :
    lam.shape ≤ γ.shape := by
  refine YoungDiagram.le_of_forall_rowLen_le fun r => ?_
  by_cases hr : r < n
  · have hfull := sum_range_hiveRowCountInt_full h hr le_rfl
    rw [apply_productVertex_diag_of_productBoundary hb (by omega),
      apply_productVertex_diag_of_productBoundary hb (by omega),
      apply_productVertex_zero_left_of_productBoundary hb (by omega),
      apply_productVertex_zero_left_of_productBoundary hb (by omega),
      filter_lt_succ_sum γ hr, filter_lt_succ_sum lam hr] at hfull
    have hnn : 0 ≤ ∑ k ∈ Finset.range (r + 1), hiveRowCountInt h r k :=
      Finset.sum_nonneg fun k _ => hiveRowCountInt_nonneg hb hμ r k
    have hle_int : lam.1 ⟨r, hr⟩ ≤ γ.1 ⟨r, hr⟩ := by linarith
    rw [← DominantWeight.natCast_rowLen_shape hlam ⟨r, hr⟩,
      ← DominantWeight.natCast_rowLen_shape hγ ⟨r, hr⟩] at hle_int
    exact Int.ofNat_le.mp hle_int
  · rw [DominantWeight.rowLen_shape_eq_zero_of_le _ (Nat.le_of_not_lt hr)]
    exact Nat.zero_le _

private theorem natCast_sum_hiveRowCount {n : ℕ} {α : Type*} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) (hμ : μ.IsPolynomial)
    (s : Finset α) (r k : α → ℕ) :
    ((∑ x ∈ s, hiveRowCount h (r x) (k x) : ℕ) : ℤ) =
      ∑ x ∈ s, hiveRowCountInt h (r x) (k x) := by
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl fun x _ => natCast_hiveRowCount hb hμ (r x) (k x)

private theorem sum_range_hiveRowCount_eq_rowLen_sub {n : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ)
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    {r m : ℕ} (hrm : r < m ∨ n ≤ m) :
    ∑ k ∈ Finset.range m, hiveRowCount h r k = γ.shape.rowLen r - lam.shape.rowLen r := by
  by_cases hr : r < n
  · have hcast := natCast_sum_hiveRowCount hb hμ (Finset.range m) (fun _ => r) (fun k => k)
    have hfull := sum_range_hiveRowCountInt_full (m := m) h hr (by omega)
    rw [apply_productVertex_diag_of_productBoundary hb (by omega),
      apply_productVertex_diag_of_productBoundary hb (by omega),
      apply_productVertex_zero_left_of_productBoundary hb (by omega),
      apply_productVertex_zero_left_of_productBoundary hb (by omega),
      filter_lt_succ_sum γ hr, filter_lt_succ_sum lam hr,
      ← DominantWeight.natCast_rowLen_shape hγ ⟨r, hr⟩,
      ← DominantWeight.natCast_rowLen_shape hlam ⟨r, hr⟩] at hfull
    have hle := YoungDiagram.rowLen_le_of_le (shape_le_of_productBoundary hb hlam hμ hγ) r
    exact Int.ofNat_inj.mp (by rw [Nat.cast_sub hle, hcast]; linarith)
  · have hnr : n ≤ r := Nat.le_of_not_lt hr
    rw [Finset.sum_eq_zero fun k _ => hiveRowCount_eq_zero_of_le h hnr,
      DominantWeight.rowLen_shape_eq_zero_of_le _ hnr,
      DominantWeight.rowLen_shape_eq_zero_of_le _ hnr]
    rfl

private theorem sum_hiveRowCount_eq_rowLen_sub {n : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ)
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial) (r : ℕ) :
    ∑ k ∈ Finset.range n, hiveRowCount h r k = γ.shape.rowLen r - lam.shape.rowLen r :=
  sum_range_hiveRowCount_eq_rowLen_sub hb hlam hμ hγ (Or.inr le_rfl)

private theorem col_strict_hiveRowCount {n : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ)
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial) (r x : ℕ) :
    lam.shape.rowLen (r + 1) + ∑ k ∈ Finset.range (x + 1), hiveRowCount h (r + 1) k ≤
      lam.shape.rowLen r + ∑ k ∈ Finset.range x, hiveRowCount h r k := by
  by_cases hr1 : r + 1 < n
  · have hr : r < n := by omega
    by_cases hxr : x ≤ r
    · have hcol_rh := h.le_of_isRhombus (isRhombus_productVertex_col hxr (by omega : r + 2 ≤ n))
      have hs1 := sum_range_hiveRowCountInt_right h (i := x + 1) (r := r + 1) (by omega) hr1
      have hs0 := sum_range_hiveRowCountInt_right h (i := x) (r := r) hxr hr
      rw [apply_productVertex_zero_left_of_productBoundary hb (by omega),
        apply_productVertex_zero_left_of_productBoundary hb (by omega),
        filter_lt_succ_sum lam hr1,
        ← DominantWeight.natCast_rowLen_shape hlam ⟨r + 1, hr1⟩] at hs1
      rw [apply_productVertex_zero_left_of_productBoundary hb (by omega),
        apply_productVertex_zero_left_of_productBoundary hb (by omega),
        filter_lt_succ_sum lam hr,
        ← DominantWeight.natCast_rowLen_shape hlam ⟨r, hr⟩] at hs0
      have hc1 :=
        natCast_sum_hiveRowCount hb hμ (Finset.range (x + 1)) (fun _ => r + 1) (fun k => k)
      have hc0 := natCast_sum_hiveRowCount hb hμ (Finset.range x) (fun _ => r) (fun k => k)
      exact Int.ofNat_le.mp (by rw [Nat.cast_add, Nat.cast_add, hc1, hc0]; linarith)
    · rw [sum_range_hiveRowCount_eq_rowLen_sub hb hlam hμ hγ (Or.inl (by omega)),
        sum_range_hiveRowCount_eq_rowLen_sub hb hlam hμ hγ (Or.inl (by omega))]
      have hle1 :=
        YoungDiagram.rowLen_le_of_le (shape_le_of_productBoundary hb hlam hμ hγ) (r + 1)
      have hle0 := YoungDiagram.rowLen_le_of_le (shape_le_of_productBoundary hb hlam hμ hγ) r
      have hanti := γ.shape.rowLen_anti r (r + 1) (Nat.le_succ r)
      omega
  · have hnr : n ≤ r + 1 := Nat.le_of_not_lt hr1
    rw [DominantWeight.rowLen_shape_eq_zero_of_le _ hnr,
      Finset.sum_eq_zero fun k _ => hiveRowCount_eq_zero_of_le h hnr, zero_add]
    exact Nat.zero_le _

private theorem ballot_hiveRowCount {n : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) (hμ : μ.IsPolynomial)
    (k x : ℕ) :
    ∑ r ∈ Finset.range (x + 1), hiveRowCount h r (k + 1) ≤
      ∑ r ∈ Finset.range x, hiveRowCount h r k := by
  by_cases hk1 : k + 1 < n
  · by_cases hkx : k < x
    · rcases lt_or_ge x n with hxn | hnx
      · have hbal_rh := h.le_of_isRhombus (isRhombus_productVertex_ballot hkx (by omega))
        have hs1 := sum_range_hiveRowCountInt_left h (k + 1) (by omega : x + 1 ≤ n)
        have hs0 := sum_range_hiveRowCountInt_left h k (by omega : x ≤ n)
        rw [dite_eq_left (by omega : k + 1 < x + 1)] at hs1; rw [dite_eq_left hkx] at hs0
        have hc1 :=
          natCast_sum_hiveRowCount hb hμ (Finset.range (x + 1)) (fun r => r) (fun _ => k + 1)
        have hc0 := natCast_sum_hiveRowCount hb hμ (Finset.range x) (fun r => r) (fun _ => k)
        exact Int.ofNat_le.mp (by rw [hc1, hc0]; linarith)
      · have hstab : ∀ m a, n ≤ m →
            ∑ r ∈ Finset.range m, hiveRowCount h r a =
              ∑ r ∈ Finset.range n, hiveRowCount h r a :=
          fun m a hm => by
            obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
            have htail : ∑ r ∈ Finset.range d, hiveRowCount h (n + r) a = 0 :=
              Finset.sum_eq_zero fun r _ => hiveRowCount_eq_zero_of_le h (by omega)
            rw [Finset.sum_range_add, htail, add_zero]
        rw [hstab (x + 1) (k + 1) (by omega), hstab x k hnx]
        have hs1 := sum_range_hiveRowCountInt_left h (k + 1) le_rfl
        have hs0 := sum_range_hiveRowCountInt_left h k le_rfl
        rw [dite_eq_left hk1, apply_productVertex_right_self_of_productBoundary hb (by omega),
          apply_productVertex_right_self_of_productBoundary hb (by omega),
          filter_lt_succ_sum μ hk1] at hs1
        rw [dite_eq_left (by omega : k < n),
          apply_productVertex_right_self_of_productBoundary hb (by omega),
          apply_productVertex_right_self_of_productBoundary hb (by omega),
          filter_lt_succ_sum μ (by omega : k < n)] at hs0
        have hc1 := natCast_sum_hiveRowCount hb hμ (Finset.range n) (fun r => r) (fun _ => k + 1)
        have hc0 := natCast_sum_hiveRowCount hb hμ (Finset.range n) (fun r => r) (fun _ => k)
        have hanti : μ.1 ⟨k + 1, hk1⟩ ≤ μ.1 ⟨k, by omega⟩ :=
          μ.antitone (Fin.mk_le_mk.mpr (Nat.le_succ k))
        exact Int.ofNat_le.mp (by rw [hc1, hc0]; linarith)
    · rw [Finset.sum_eq_zero fun r hr =>
        hiveRowCount_eq_zero_of_lt h (by have := Finset.mem_range.mp hr; omega)]
      exact Nat.zero_le _
  · rw [Finset.sum_eq_zero fun r _ => by
      by_cases hr : r < n
      · exact hiveRowCount_eq_zero_of_lt h (by omega)
      · exact hiveRowCount_eq_zero_of_le h (Nat.le_of_not_lt hr)]
    exact Nat.zero_le _

/-- Reconstruct the Littlewood–Richardson tableau of shape `γ.shape / λ.shape` and content
`μ.shape` from an integer hive with boundary `productBoundary λ μ γ`. -/
def lrTableauOfHive {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    LRTableau lam.shape γ.shape μ.shape := by
  let S : SkewSemistandardYoungTableau lam.shape γ.shape :=
    SkewSemistandardYoungTableau.ofRowCount
      (shape_le_of_productBoundary h.2 hlam hμ hγ) n (hiveRowCount h.1)
      (sum_hiveRowCount_eq_rowLen_sub h.2 hlam hμ hγ)
      (col_strict_hiveRowCount h.2 hlam hμ hγ)
  have hrc : ∀ r k, S.rowCount r k = hiveRowCount h.1 r k :=
    SkewSemistandardYoungTableau.rowCount_ofRowCount
      (shape_le_of_productBoundary h.2 hlam hμ hγ)
      (sum_hiveRowCount_eq_rowLen_sub h.2 hlam hμ hγ)
      (col_strict_hiveRowCount h.2 hlam hμ hγ)
      (fun r k hnk => by
        by_cases hr : r < n
        · exact hiveRowCount_eq_zero_of_lt h.1 (by omega)
        · exact hiveRowCount_eq_zero_of_le h.1 (Nat.le_of_not_lt hr))
  refine ⟨S, funext fun k => ?_, ?_⟩
  · rw [← S.sum_range_rowCount_eq_content k (DominantWeight.colLen_zero_shape_le γ),
      Finset.sum_congr rfl fun r _ => hrc r k]
    by_cases hk : k < n
    · have hs := sum_range_hiveRowCountInt_left h.1 k le_rfl
      rw [dite_eq_left hk, apply_productVertex_right_self_of_productBoundary h.2 (by omega),
        apply_productVertex_right_self_of_productBoundary h.2 (by omega),
        filter_lt_succ_sum μ hk, ← DominantWeight.natCast_rowLen_shape hμ ⟨k, hk⟩] at hs
      have hc := natCast_sum_hiveRowCount h.2 hμ (Finset.range n) (fun r => r) (fun _ => k)
      exact Int.ofNat_inj.mp (by rw [hc]; linarith)
    · rw [DominantWeight.rowLen_shape_eq_zero_of_le μ (Nat.le_of_not_lt hk)]
      exact Finset.sum_eq_zero fun r hr =>
        hiveRowCount_eq_zero_of_lt h.1 (lt_of_lt_of_le (Finset.mem_range.mp hr) (by omega))
  · rw [S.isLatticeWord_readingWord_iff]
    intro k x
    simp only [hrc]
    exact ballot_hiveRowCount h.2 hμ k x

@[simp] theorem rowCount_lrTableauOfHive {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) (r k : ℕ) :
    (lrTableauOfHive hlam hμ hγ h).1.rowCount r k = hiveRowCount h.1 r k :=
  SkewSemistandardYoungTableau.rowCount_ofRowCount
    (shape_le_of_productBoundary h.2 hlam hμ hγ)
    (sum_hiveRowCount_eq_rowLen_sub h.2 hlam hμ hγ)
    (col_strict_hiveRowCount h.2 hlam hμ hγ)
    (fun r' k' hnk => by
      by_cases hr' : r' < n
      · exact hiveRowCount_eq_zero_of_lt h.1 (by omega)
      · exact hiveRowCount_eq_zero_of_le h.1 (Nat.le_of_not_lt hr')) r k

/-- **The hive-to-Littlewood–Richardson equivalence** for polynomial dominant weights `λ, μ, γ`:
an explicit bijection between normalized integer hives with clockwise boundary `(λ, μ, γ*)` and
Littlewood–Richardson tableaux of shape `γ.shape / λ.shape` and content `μ.shape`. -/
def fixedIntegerHiveEquivLRTableau {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial) :
    FixedIntegerHive (productBoundary lam μ γ) ≃ LRTableau lam.shape γ.shape μ.shape where
  toFun := lrTableauOfHive hlam hμ hγ
  invFun := fixedIntegerHiveOfLRTableau hlam hμ hγ
  left_inv h := by
    apply Subtype.ext; ext p
    rw [← Vertex.productVertex_z_add p, coe_fixedIntegerHiveOfLRTableau,
      hiveOfLRTableau_productVertex]
    simp only [rowCount_lrTableauOfHive, natCast_hiveRowCount h.2 hμ]
    rw [sum_range_sum_range_hiveRowCountInt h.1 (Nat.le_add_left _ _)
        (by have := p.sum_eq; omega),
      apply_productVertex_zero_left_of_productBoundary h.2 (by have := p.sum_eq; omega)]
    abel
  right_inv T := by
    apply Subtype.ext
    refine SkewSemistandardYoungTableau.eq_of_rowCount_eq fun r k => ?_
    rw [rowCount_lrTableauOfHive, coe_fixedIntegerHiveOfLRTableau,
      hiveRowCount_hiveOfLRTableau hlam (DominantWeight.colLen_zero_shape_le γ) T]

@[simp] theorem fixedIntegerHiveEquivLRTableau_apply {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    fixedIntegerHiveEquivLRTableau hlam hμ hγ h = lrTableauOfHive hlam hμ hγ h := (rfl)

@[simp] theorem fixedIntegerHiveEquivLRTableau_symm_apply {n : ℕ} {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial)
    (T : LRTableau lam.shape γ.shape μ.shape) :
    (fixedIntegerHiveEquivLRTableau hlam hμ hγ).symm T =
      fixedIntegerHiveOfLRTableau hlam hμ hγ T := (rfl)

/-- Young-diagram form of the hive-to-LR equivalence on `weightOfShape n` for diagrams of at most
`n` rows. -/
def fixedIntegerHiveWeightOfShapeEquivLRTableau {n : ℕ} {lam μ ν : YoungDiagram}
    (hlam : lam.colLen 0 ≤ n) (hμ : μ.colLen 0 ≤ n) (hν : ν.colLen 0 ≤ n) :
    FixedIntegerHive
      (productBoundary (weightOfShape n lam) (weightOfShape n μ) (weightOfShape n ν)) ≃
      LRTableau lam ν μ :=
  (fixedIntegerHiveEquivLRTableau (isPolynomial_weightOfShape n lam)
    (isPolynomial_weightOfShape n μ) (isPolynomial_weightOfShape n ν)).trans
    (by rw [shape_weightOfShape hlam, shape_weightOfShape hμ, shape_weightOfShape hν])

end InverseMap

/-! ### Affine determinant shifts and arbitrary signed dominant weights -/

section DeterminantShift

@[simp] theorem affine_add {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] (β₁ γ₁ β₂ γ₂ : R) :
    affine n (β₁ + β₂) (γ₁ + γ₂) = affine n β₁ γ₁ + affine n β₂ γ₂ := by
  ext p
  simp only [affine_apply, add_apply, smul_add]
  abel

@[simp] theorem affine_zero (n : ℕ) (R : Type*) [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] : affine n (0 : R) 0 = 0 := by
  ext p; simp

/-- Adding `Hive.affine n a (a + b)` shifts `productBoundary lam μ γ` to
`productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b))`. -/
theorem boundary_add_affine_shift {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (a b : ℤ) :
    (h + affine n a (a + b)).boundary =
      productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b)) := by
  ext s i
  rw [boundary_add, Pi.add_apply, hb, boundary_affine]
  fin_cases s
  · simp
  · simp only [Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      productBoundary_one, DominantWeight.shift_apply, Pi.add_apply]
    abel
  · simp only [Fin.reduceFinMk, Matrix.cons_val, productBoundary_two, DominantWeight.dual_apply,
      DominantWeight.shift_apply, Pi.add_apply]
    abel

/-- **Affine determinant-shift equivalence on integer hives**: adding `affine n a (a + b)` is a
bijection between `FixedIntegerHive (productBoundary lam μ γ)` and
`FixedIntegerHive (productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b)))`. -/
def fixedIntegerHiveShiftEquiv {n : ℕ} (lam μ γ : DominantWeight n) (a b : ℤ) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      FixedIntegerHive (productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b))) where
  toFun h := ⟨h.1 + affine n a (a + b), boundary_add_affine_shift h.2 a b⟩
  invFun h :=
    ⟨h.1 + affine n (-a) (-a + -b), by
      have hab : a + b + (-a + -b) = 0 := by ring
      rw [boundary_add_affine_shift h.2 (-a) (-b), DominantWeight.shift_shift,
        DominantWeight.shift_shift, DominantWeight.shift_shift]
      simp [hab]⟩
  left_inv h := by
    apply Subtype.ext; ext p
    simp only [add_apply, affine_apply]
    ring
  right_inv h := by
    apply Subtype.ext; ext p
    simp only [add_apply, affine_apply]
    ring

@[simp] theorem coe_fixedIntegerHiveShiftEquiv_apply {n : ℕ} (lam μ γ : DominantWeight n)
    (a b : ℤ) (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveShiftEquiv lam μ γ a b h).1 = h.1 + affine n a (a + b) := (rfl)

/-- **Determinant-shift covariance of `hiveCount`**: shifting `λ` by `a` and `μ` by `b` while
shifting `γ` by `a + b` preserves `hiveCount`. -/
@[simp] theorem hiveCount_productBoundary_shift {n : ℕ} (lam μ γ : DominantWeight n) (a b : ℤ) :
    hiveCount (productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b))) =
      hiveCount (productBoundary lam μ γ) := by
  rw [← card_fixedIntegerHive, ← card_fixedIntegerHive]
  exact Fintype.card_congr (fixedIntegerHiveShiftEquiv lam μ γ a b).symm

theorem hiveCount_productBoundary_shift_left {n : ℕ} (lam μ γ : DominantWeight n) (a : ℤ) :
    hiveCount (productBoundary (lam.shift a) μ (γ.shift a)) =
      hiveCount (productBoundary lam μ γ) := by
  simpa using hiveCount_productBoundary_shift lam μ γ a 0

theorem hiveCount_productBoundary_shift_right {n : ℕ} (lam μ γ : DominantWeight n) (b : ℤ) :
    hiveCount (productBoundary lam (μ.shift b) (γ.shift b)) =
      hiveCount (productBoundary lam μ γ) := by
  simpa using hiveCount_productBoundary_shift lam μ γ 0 b

/-- When `γ.detShift < lam.detShift + μ.detShift`, no integer hive has boundary
`productBoundary lam μ γ`. -/
theorem isEmpty_fixedIntegerHive_of_detShift_lt {n : ℕ} {lam μ γ : DominantWeight n}
    (hdet : γ.detShift < lam.detShift + μ.detShift) :
    IsEmpty (FixedIntegerHive (productBoundary lam μ γ)) :=
  ⟨fun ⟨_, hb⟩ => (not_le_of_gt hdet) (detShift_le_of_productBoundary hb)⟩

theorem hiveCount_productBoundary_eq_zero_of_detShift_lt {n : ℕ} {lam μ γ : DominantWeight n}
    (hdet : γ.detShift < lam.detShift + μ.detShift) :
    hiveCount (productBoundary lam μ γ) = 0 :=
  hiveCount_eq_zero_iff.mpr (isEmpty_fixedIntegerHive_of_detShift_lt hdet)

/-- Adding `affine n a (a + b)` leaves off-diagonal `hiveRowCountInt` unchanged and adds `b` to
each diagonal entry `r < n`. -/
theorem hiveRowCountInt_add_affine_shift {n : ℕ} (h : Hive n ℤ) (a b : ℤ) (r k : ℕ) :
    hiveRowCountInt (h + affine n a (a + b)) r k =
      hiveRowCountInt h r k + if r < n ∧ k = r then b else 0 := by
  by_cases hr : r < n
  · rcases lt_trichotomy k r with hkr | rfl | hrk
    · have hne : k ≠ r := ne_of_lt hkr
      simp only [hr, hne, and_false, ↓reduceIte, add_zero, hiveRowCountInt_of_lt _ hkr hr,
        add_apply, affine_apply, Vertex.productVertex_y, Vertex.productVertex_z, nsmul_eq_mul]
      have hy00 : ((r - k : ℕ) : ℤ) = (r : ℤ) - k := by omega
      have hy10 : ((r - (k + 1) : ℕ) : ℤ) = (r : ℤ) - k - 1 := by omega
      have hy11 : ((r + 1 - (k + 1) : ℕ) : ℤ) = (r : ℤ) - k := by omega
      have hy01 : ((r + 1 - k : ℕ) : ℤ) = (r : ℤ) - k + 1 := by omega
      rw [hy00, hy10, hy11, hy01]
      push_cast; ring
    · simp only [hr, true_and, ↓reduceIte, hiveRowCountInt_diag _ hr, add_apply, affine_apply,
        Vertex.productVertex_y, Vertex.productVertex_z, Nat.sub_self, Nat.add_sub_cancel_left,
        nsmul_eq_mul]
      push_cast; ring
    · have hne : k ≠ r := ne_of_gt hrk
      simp [hr, hne, hiveRowCountInt_eq_zero_of_lt _ hrk]
  · simp [hr, hiveRowCountInt_eq_zero_of_le _ (Nat.le_of_not_lt hr)]

/-- **Canonical signed hive-to-LR equivalence**: for arbitrary signed dominant weights `λ, μ, γ`
satisfying `λ.detShift + μ.detShift ≤ γ.detShift`, subtracting `λ.detShift` and `μ.detShift`
identifies `FixedIntegerHive (productBoundary λ μ γ)` with the Littlewood–Richardson tableaux of
shape `(γ.shift (-(λ.detShift + μ.detShift))).shape / λ.detShiftShape` and content
`μ.detShiftShape`. -/
def fixedIntegerHiveSignedEquivLRTableau {n : ℕ} {lam μ γ : DominantWeight n}
    (hdet : lam.detShift + μ.detShift ≤ γ.detShift) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      LRTableau lam.detShiftShape (γ.shift (-(lam.detShift + μ.detShift))).shape
        μ.detShiftShape := by
  have hγ_poly : (γ.shift (-lam.detShift + -μ.detShift)).IsPolynomial := by
    rw [DominantWeight.isPolynomial_iff_zero_le_detShift]
    cases n with
    | zero => simp
    | succ m =>
      rw [DominantWeight.detShift_shift]
      linarith [hdet]
  have hneg : -lam.detShift + -μ.detShift = -(lam.detShift + μ.detShift) := by ring
  have hshape : ∀ l : DominantWeight n, (l.shift (-l.detShift)).shape = l.detShiftShape :=
    fun l => by
      rw [← DominantWeight.weightOfShape_detShiftShape,
        shape_weightOfShape l.colLen_zero_detShiftShape_le]
  exact (fixedIntegerHiveShiftEquiv lam μ γ (-lam.detShift) (-μ.detShift)).trans <|
    (fixedIntegerHiveEquivLRTableau
      (DominantWeight.isPolynomial_shift_neg_detShift lam)
      (DominantWeight.isPolynomial_shift_neg_detShift μ) hγ_poly).trans
    (Equiv.cast (by rw [hshape lam, hshape μ, hneg]))

/-- **Shift independence on the tableau carrier**: for any two shift pairs `(a₁, b₁)` and
`(a₂, b₂)` making all three shifted weights polynomial, the corresponding Littlewood–Richardson
tableau types are canonically in bijection via `fixedIntegerHiveShiftEquiv`. -/
def lrTableauShiftEquiv {n : ℕ} (lam μ γ : DominantWeight n) (a₁ b₁ a₂ b₂ : ℤ)
    (hlam₁ : (lam.shift a₁).IsPolynomial) (hμ₁ : (μ.shift b₁).IsPolynomial)
    (hγ₁ : (γ.shift (a₁ + b₁)).IsPolynomial)
    (hlam₂ : (lam.shift a₂).IsPolynomial) (hμ₂ : (μ.shift b₂).IsPolynomial)
    (hγ₂ : (γ.shift (a₂ + b₂)).IsPolynomial) :
    LRTableau (lam.shift a₁).shape (γ.shift (a₁ + b₁)).shape (μ.shift b₁).shape ≃
      LRTableau (lam.shift a₂).shape (γ.shift (a₂ + b₂)).shape (μ.shift b₂).shape :=
  (fixedIntegerHiveEquivLRTableau hlam₁ hμ₁ hγ₁).symm.trans <|
    (fixedIntegerHiveShiftEquiv lam μ γ a₁ b₁).symm.trans <|
      (fixedIntegerHiveShiftEquiv lam μ γ a₂ b₂).trans
        (fixedIntegerHiveEquivLRTableau hlam₂ hμ₂ hγ₂)

/-- Explicit row-count formula for `lrTableauShiftEquiv`: off-diagonal counts are invariant under
arbitrary determinant shifts, while diagonal counts in rows `r < n` shift by `b₂ - b₁`. -/
theorem rowCount_lrTableauShiftEquiv {n : ℕ} (lam μ γ : DominantWeight n) (a₁ b₁ a₂ b₂ : ℤ)
    (hlam₁ : (lam.shift a₁).IsPolynomial) (hμ₁ : (μ.shift b₁).IsPolynomial)
    (hγ₁ : (γ.shift (a₁ + b₁)).IsPolynomial)
    (hlam₂ : (lam.shift a₂).IsPolynomial) (hμ₂ : (μ.shift b₂).IsPolynomial)
    (hγ₂ : (γ.shift (a₂ + b₂)).IsPolynomial)
    (T : LRTableau (lam.shift a₁).shape (γ.shift (a₁ + b₁)).shape (μ.shift b₁).shape)
    (r k : ℕ) :
    ((lrTableauShiftEquiv lam μ γ a₁ b₁ a₂ b₂ hlam₁ hμ₁ hγ₁ hlam₂ hμ₂ hγ₂ T).1.rowCount r k :
        ℤ) =
      (T.1.rowCount r k : ℤ) + if r < n ∧ k = r then b₂ - b₁ else 0 := by
  set T' :=
    lrTableauShiftEquiv lam μ γ a₁ b₁ a₂ b₂ hlam₁ hμ₁ hγ₁ hlam₂ hμ₂ hγ₂ T
  let h₁ := fixedIntegerHiveOfLRTableau hlam₁ hμ₁ hγ₁ T
  let h₂ := fixedIntegerHiveShiftEquiv lam μ γ a₂ b₂
    ((fixedIntegerHiveShiftEquiv lam μ γ a₁ b₁).symm h₁)
  have hT' : T' = lrTableauOfHive hlam₂ hμ₂ hγ₂ h₂ := rfl
  have hh₂ : h₂.1 = h₁.1 + affine n (a₂ - a₁) ((a₂ - a₁) + (b₂ - b₁)) := by
    ext p
    simp only [h₂, h₁, fixedIntegerHiveShiftEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
      add_apply, affine_apply]
    ring
  rw [hT', rowCount_lrTableauOfHive, natCast_hiveRowCount h₂.2 hμ₂, hh₂,
    hiveRowCountInt_add_affine_shift, ← natCast_hiveRowCount h₁.2 hμ₁,
    coe_fixedIntegerHiveOfLRTableau,
    hiveRowCount_hiveOfLRTableau hlam₁ (DominantWeight.colLen_zero_shape_le _) T]

end DeterminantShift

/-! ### Concrete checks in ranks `2` and `3` -/

section Checks

/-- **Rank-`2` check (`λ = μ = (1, 0)`, `γ = (1, 1)`)**: `detTwo` corresponds under
`fixedIntegerHiveEquivLRTableau` to the unique LR tableau of shape `(1, 1) / (1)` and content
`(1)`, with `rowCount 1 0 = 1`, `detTwo(1, 1) = 1`, and `detTwo(1, 2) = 2`. -/
theorem rowCount_lrTableau_detTwo :
    let lam : DominantWeight 2 := ⟨![1, 0], by decide⟩
    let γ : DominantWeight 2 := ⟨![1, 1], by decide⟩
    let hlam : lam.IsPolynomial := by
      rw [DominantWeight.isPolynomial_iff_zero_le_detShift, DominantWeight.detShift_succ]; decide
    let hγ : γ.IsPolynomial := by
      rw [DominantWeight.isPolynomial_iff_zero_le_detShift, DominantWeight.detShift_succ]; decide
    let T := fixedIntegerHiveEquivLRTableau hlam hlam hγ ⟨detTwo, boundary_detTwo⟩
    T.1.rowCount 1 0 = 1 ∧
      detTwo (Vertex.productVertex 2 1 1 le_rfl (by decide)) = 1 ∧
      detTwo (Vertex.productVertex 2 1 2 (by decide) le_rfl) = 2 := by
  refine ⟨?_, by simp, by simp⟩
  rw [fixedIntegerHiveEquivLRTableau_apply, rowCount_lrTableauOfHive, hiveRowCount,
    hiveRowCountInt_of_lt _ (by decide) (by decide)]
  simp

private theorem eq_of_apply_interior_three {B : Fin 3 → Fin 3 → ℤ}
    {h₁ h₂ : FixedIntegerHive B}
    (hv : h₁.1 ⟨1, 1, 1, rfl⟩ = h₂.1 ⟨1, 1, 1, rfl⟩) : h₁ = h₂ := by
  apply Subtype.ext; ext p
  have hp := p.sum_eq
  rcases (by omega : p.z = 0 ∨ p.x = 0 ∨ p.y = 0 ∨ (p.x = 1 ∧ p.y = 1 ∧ p.z = 1)) with
    hz | hx | hy | ⟨hx, hy, hz⟩
  · have hp' : p = Vertex.edgePoint 3 0 ⟨p.y, by omega⟩ := by ext <;> simp [hz]; omega
    rw [hp', apply_edgePoint_zero, apply_edgePoint_zero, h₁.2, h₂.2]
  · have hp' : p = Vertex.edgePoint 3 1 ⟨p.z, by omega⟩ := by ext <;> simp [hx]; omega
    rw [hp', apply_edgePoint_one, apply_edgePoint_one, h₁.2, h₂.2]
  · have hp' : p = Vertex.edgePoint 3 2 ⟨p.x, by omega⟩ := by ext <;> simp [hy]; omega
    rw [hp', apply_edgePoint_two, apply_edgePoint_two, h₁.2, h₂.2]
  · have hp' : p = ⟨1, 1, 1, rfl⟩ := by ext <;> simp [hx, hy, hz]
    rw [hp', hv]

private theorem apply_interior_three_bounds {lam μ γ : DominantWeight 3}
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    lam.1 1 + γ.1 0 ≤ h.1 ⟨1, 1, 1, rfl⟩ ∧
      h.1 ⟨1, 1, 1, rfl⟩ ≤ lam.1 0 + lam.1 1 + μ.1 0 := by
  have hp12 : (⟨1, 1, 1, rfl⟩ : Vertex 3) =
      Vertex.productVertex 3 1 2 (by decide) (by decide) := rfl
  have hlo := h.1.le_of_isRhombus
    (isRhombus_productVertex_mixed (n := 3) (i := 0) (j := 1) (by decide) (by decide))
  have hhi := h.1.le_of_isRhombus
    (isRhombus_productVertex_mixed (n := 3) (i := 0) (j := 2) (by decide) (by decide))
  rw [apply_productVertex_zero_left_of_productBoundary h.2 (by decide),
    apply_productVertex_zero_left_of_productBoundary h.2 (by decide),
    apply_productVertex_diag_of_productBoundary h.2 (by decide), ← hp12] at hlo
  rw [apply_productVertex_zero_left_of_productBoundary h.2 (by decide),
    apply_productVertex_zero_left_of_productBoundary h.2 (by decide),
    apply_productVertex_right_self_of_productBoundary h.2 (by decide), ← hp12] at hhi
  simp only [Finset.sum_filter, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
    at hlo hhi
  omega

private def threeFun (lam μ γ : Fin 3 → ℤ) (v : ℤ) (p : Vertex 3) : ℤ :=
  match p.z, p.y + p.z with
  | 0, 0 => 0
  | 0, 1 => lam 0
  | 0, 2 => lam 0 + lam 1
  | 0, _ => lam 0 + lam 1 + lam 2
  | 1, 1 => γ 0
  | 1, 2 => v
  | 1, _ => lam 0 + lam 1 + lam 2 + μ 0
  | 2, 2 => γ 0 + γ 1
  | 2, _ => lam 0 + lam 1 + lam 2 + μ 0 + μ 1
  | _, _ => γ 0 + γ 1 + γ 2

/-- **Rank-`3` check `c^{(2, 0, 0)}_{(1, 0, 0), (1, 0, 0)} = 1`**. -/
theorem hiveCount_three_one_one_two :
    hiveCount
      (productBoundary ⟨![1, 0, 0], by decide⟩ ⟨![1, 0, 0], by decide⟩
        ⟨![2, 0, 0], by decide⟩) = 1 := by
  rw [← card_fixedIntegerHive]
  let lam : DominantWeight 3 := ⟨![1, 0, 0], by decide⟩
  let γ : DominantWeight 3 := ⟨![2, 0, 0], by decide⟩
  let f := threeFun lam.1 lam.1 γ.1 2
  have hf : IsRhombusConcave f := by
    refine (isRhombusConcave_iff_productVertex f).mpr ⟨?_, ?_, ?_⟩
    · intro i j hij hj
      rcases (by omega : i = 0 ∧ j = 1 ∨ i = 0 ∧ j = 2 ∨ i = 1 ∧ j = 2) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [f, threeFun, lam, γ]
    · intro i j hij hj
      rcases (by omega : i = 0 ∧ j = 0 ∨ i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 1) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [f, threeFun, lam, γ]
    · intro i j hij hj
      rcases (by omega : i = 0 ∧ j = 1 ∨ i = 0 ∧ j = 2 ∨ i = 1 ∧ j = 2) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [f, threeFun, lam, γ]
  let h₀ : FixedIntegerHive (productBoundary lam lam γ) :=
    ⟨⟨f, by simp [f, threeFun], fun hr => (isRhombusConcave_def f).mp hf hr⟩, by
      ext s m; fin_cases s <;> fin_cases m <;> simp [boundary_apply, f, threeFun, lam, γ]⟩
  refine Fintype.card_eq_one_iff.mpr ⟨h₀, fun h => eq_of_apply_interior_three ?_⟩
  have hb := apply_interior_three_bounds h
  have hh₀ : h₀.1 ⟨1, 1, 1, rfl⟩ = 2 := by simp [h₀, f, threeFun]
  dsimp only [lam, γ] at hb
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hb
  rw [hh₀]
  omega

/-- **Rank-`3` ballot check `c^{(3, 2, 1)}_{(2, 1, 0), (2, 1, 0)} = 2`**: the two hives correspond
to interior values `h(1, 2) = 4` (reading word `010`) and `h(1, 2) = 5` (reading word `001`), while
`100` is excluded by the ballot condition. -/
theorem hiveCount_three_two_one_two_one_three_two_one :
    hiveCount
      (productBoundary ⟨![2, 1, 0], by decide⟩ ⟨![2, 1, 0], by decide⟩
        ⟨![3, 2, 1], by decide⟩) = 2 := by
  rw [← card_fixedIntegerHive]
  let lam : DominantWeight 3 := ⟨![2, 1, 0], by decide⟩
  let γ : DominantWeight 3 := ⟨![3, 2, 1], by decide⟩
  let mkHive (v : ℤ) (hv4 : 4 ≤ v) (hv5 : v ≤ 5) :
      FixedIntegerHive (productBoundary lam lam γ) := by
    let f := threeFun lam.1 lam.1 γ.1 v
    have hf : IsRhombusConcave f := by
      refine (isRhombusConcave_iff_productVertex f).mpr ⟨?_, ?_, ?_⟩
      · intro i j hij hj
        rcases (by omega : i = 0 ∧ j = 1 ∨ i = 0 ∧ j = 2 ∨ i = 1 ∧ j = 2) with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [f, threeFun, lam, γ] <;> omega
      · intro i j hij hj
        rcases (by omega : i = 0 ∧ j = 0 ∨ i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 1) with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [f, threeFun, lam, γ] <;> omega
      · intro i j hij hj
        rcases (by omega : i = 0 ∧ j = 1 ∨ i = 0 ∧ j = 2 ∨ i = 1 ∧ j = 2) with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [f, threeFun, lam, γ] <;> omega
    exact ⟨⟨f, by simp [f, threeFun], fun hr => (isRhombusConcave_def f).mp hf hr⟩, by
      ext s m; fin_cases s <;> fin_cases m <;> simp [boundary_apply, f, threeFun, lam, γ]⟩
  refine (Fintype.card_congr
    { toFun := fun h => decide (h.1 ⟨1, 1, 1, rfl⟩ = 5)
      invFun := fun b => if b then mkHive 5 (by omega) le_rfl else mkHive 4 le_rfl (by omega)
      left_inv := fun h => by
        have hb := apply_interior_three_bounds h
        dsimp only [lam, γ] at hb
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hb
        rcases (by omega : h.1 ⟨1, 1, 1, rfl⟩ = 4 ∨ h.1 ⟨1, 1, 1, rfl⟩ = 5) with hv4 | hv5
        · have hdec : decide ((4 : ℤ) = 5) = false := by decide
          simp only [hv4, hdec, Bool.false_eq_true, ↓reduceIte]
          exact eq_of_apply_interior_three hv4.symm
        · simp only [hv5, decide_true, ↓reduceIte]
          exact eq_of_apply_interior_three hv5.symm
      right_inv := fun b => by cases b <;> rfl }).trans Fintype.card_bool

/-- **Signed rank-`2` check**: `λ = (1, 0)`, `μ = (0, -1)`, `γ = (0, 0)` has `hiveCount = 1`
(`V ⊗ V*` contains the trivial representation once), whereas truncating the negative entry of `μ`
to `0` gives `((1, 0), (0, 0), (0, 0))` with `hiveCount = 0`. -/
theorem hiveCount_two_signed_std_dual_triv :
    hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![0, -1], by decide⟩ ⟨![0, 0], by decide⟩) = 1 ∧
    hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![0, 0], by decide⟩ ⟨![0, 0], by decide⟩) = 0 := by
  refine ⟨?_, hiveCount_eq_zero_of_sum_ne_zero ?_⟩
  · have hshift := hiveCount_productBoundary_shift_right
      (⟨![1, 0], by decide⟩ : DominantWeight 2) ⟨![0, -1], by decide⟩ ⟨![0, 0], by decide⟩ 1
    have hμ : DominantWeight.shift ⟨![0, -1], by decide⟩ 1 =
        (⟨![1, 0], by decide⟩ : DominantWeight 2) := by
      ext i; fin_cases i <;> simp
    have hγ : DominantWeight.shift ⟨![0, 0], by decide⟩ 1 =
        (⟨![1, 1], by decide⟩ : DominantWeight 2) := by
      ext i; fin_cases i <;> simp
    rw [hμ, hγ] at hshift
    exact hshift.symm.trans hiveCount_two_std_std_det
  · rw [Ne, sum_productBoundary_eq_zero_iff]
    simp [Fin.sum_univ_two]

end Checks

end TauCeti.Hive
