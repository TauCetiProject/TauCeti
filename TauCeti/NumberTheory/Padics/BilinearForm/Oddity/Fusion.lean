/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.LinearAlgebra.BilinearForm.Characteristic
public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Replace
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.NumberTheory.Padics.BilinearForm.Oddity.Basic
import TauCeti.NumberTheory.Padics.DyadicUnits
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Oddity fusion on dyadic Jordan splittings

Let `B` be a symmetric form on a finite free `ℤ_[2]`-module with a Jordan splitting `N` with
respect to `2`, so that `B` is `2 ^ i` times a unimodular form `C i` on `N i`. In the Conway–Sloane
calculus of `2`-adic symbols, a *compartment* is a run of consecutive constituents of type I, and
the total oddity of a compartment is preserved by *oddity fusion* with constituent signs fixed.
Sign walking can change both the signs and the total oddity. This file proves the elementary
move behind these operations on every Jordan splitting, between two adjacent constituents `N k`
and `N (k + 1)` of type I.

Let `x ∈ N k` and `y ∈ N (k + 1)` with `B x x = 2 ^ k a` and `B y y = 2 ^ (k + 1) b` for units `a`
and `b`. The vectors `x + y` and `-2 b x + a y` are orthogonal and span the same submodule as `x`
and `y`, which is the isometry `⟨a, 2 b⟩ ≅ ⟨a + 2 b, 2 a b (a + 2 b)⟩`
(`LinearMap.BilinForm.equivalent_toBilin'_diagonal_fin_two`).
Exchanging these blocks gives a Jordan splitting `N'` of `B` agreeing with `N` away from `k` and
`k + 1`, in which the Gram determinants of both constituents are multiplied by `a (a + 2 b)` up to
squares, and the oddities of the unimodular rescalings of `N k` and `N (k + 1)` change by `2 b` and
`2 a` modulo `8`. Since `a` and `b` are odd, there are two cases:

* if `a + b ≡ 0` modulo `4`, then `a (a + 2 b) ≡ -1` modulo `8`, so the signs `χ₈(det C i)` are
  unchanged and an oddity of `2 b` moves from `N (k + 1)` to `N k`
  (`LinearMap.BilinForm.IsJordanSplitting.exists_oddityFusion_succ`);
* if `a ≡ b` modulo `4`, then `a (a + 2 b) ≡ 3` modulo `8`, so both signs change and the total
  oddity changes by `4 b ≡ 4`: this is sign walking between adjacent constituents of type I
  (`LinearMap.BilinForm.IsJordanSplitting.exists_signWalk_succ_of_odd_of_odd`).

For example `⟨1⟩ ⊥ ⟨14⟩ ≅ ⟨7⟩ ⊥ ⟨2⟩` by the first move: the constituents of index `0` have the
same sign but different determinant classes: their individual oddities `1` and `7` differ, while
their totals with the oddities `7` and `1` of the constituents of index `1` agree under this
sign-preserving fusion move. The vectors `x` and `y` are part of the data, since which case occurs
depends on their norms, and both cases need not be available. In `⟨1⟩ ⊥ ⟨6⟩` every unit value
`x₁ ^ 2 + 6 x₂ ^ 2` is `1` or `7` modulo `8`, so no Jordan splitting has a constituent of index `0`
of sign `-1`: sign walking between the two constituents is impossible there, and only oddity fusion
is available.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.exists_oddityFusion_succ`: oddity fusion between adjacent
  constituents of type I.
* `LinearMap.BilinForm.IsJordanSplitting.exists_signWalk_succ_of_odd_of_odd`: sign walking between
  adjacent constituents of type I.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.5, for
  compartments, oddity fusion and sign walking.
* D. Allcock, I. Gal and A. Mark, *The Conway–Sloane calculus for 2-adic lattices*, §4.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
-/

public section

open Module
open LinearMap (BilinForm)
open PadicInt

namespace LinearMap.BilinForm

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {B : BilinForm ℤ_[2] M}
  {N : ℕ → Submodule ℤ_[2] M}

/-- **The move between adjacent constituents of type I.** For `x ∈ N k` and `y ∈ N (k + 1)` with
`B x x = 2 ^ k a` and `B y y = 2 ^ (k + 1) b`, `a` and `b` units, exchanging `x, y` for
`x + y, -2 b x + a y` gives a Jordan splitting in which the Gram determinants of both constituents
change by `a (a + 2 b)` up to squares, hence by any `c` with `c a (a + 2 b)` a square, and the
oddities of the two constituents change by `2 b` and `2 a` modulo `8`. -/
private theorem IsJordanSplitting.exists_fusion_succ [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k : ℕ} {x y : M}
    (hx : x ∈ N k) (hy : y ∈ N (k + 1)) {a b : ℤ_[2]} (ha : IsUnit a) (hb : IsUnit b)
    (hxx : B x x = 2 ^ k * a) (hyy : B y y = 2 ^ (k + 1) * b) {c : ℤ_[2]}
    (hc : IsSquare (c * a * (a + 2 * b))) :
    ∃ N' : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 N' ∧
      (∀ i, i ≠ k → i ≠ k + 1 → N' i = N i) ∧
      (∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N k)) (d' : Basis (Fin n) ℤ_[2] (N' k)),
        IsSquare (c * ((B.restrict (N k)).toMatrix d).det *
          ((B.restrict (N' k)).toMatrix d').det)) ∧
      (∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N (k + 1))) (d' : Basis (Fin n) ℤ_[2] (N' (k + 1))),
        IsSquare (c * ((B.restrict (N (k + 1))).toMatrix d).det *
          ((B.restrict (N' (k + 1))).toMatrix d').det)) ∧
      (∀ (C : BilinForm ℤ_[2] (N k)) (C' : BilinForm ℤ_[2] (N' k)) (w : N k) (w' : N' k),
        (2 : ℤ_[2]) ^ k • C = B.restrict (N k) → (2 : ℤ_[2]) ^ k • C' = B.restrict (N' k) →
        C.IsCharacteristic w → C'.IsCharacteristic w' → (8 : ℤ_[2]) ∣ C' w' w' - C w w - 2 * b) ∧
      ∀ (C : BilinForm ℤ_[2] (N (k + 1))) (C' : BilinForm ℤ_[2] (N' (k + 1))) (w : N (k + 1))
        (w' : N' (k + 1)), (2 : ℤ_[2]) ^ (k + 1) • C = B.restrict (N (k + 1)) →
        (2 : ℤ_[2]) ^ (k + 1) • C' = B.restrict (N' (k + 1)) →
        C.IsCharacteristic w → C'.IsCharacteristic w' → (8 : ℤ_[2]) ∣ C' w' w' - C w w - 2 * a := by
  have h2 : (2 : ℤ_[2]) ∈ nonZeroDivisors ℤ_[2] := mem_nonZeroDivisors_of_ne_zero two_ne_zero
  have hxy : B x y = 0 := h.apply_eq_zero k (k + 1) (by omega) x hx y hy
  -- `a + 2 b` is a unit, since `a` is.
  have ha' : IsUnit (a + 2 * b) := by
    rw [isUnit_iff_toZModPow_three_mul_self] at ha hb ⊢
    simp only [map_add, map_mul, map_ofNat]
    generalize toZModPow 3 a = A at ha ⊢
    generalize toZModPow 3 b = B at hb ⊢
    revert A B
    decide
  have hb' : IsUnit (a * b * (a + 2 * b)) := (ha.mul hb).mul ha'
  have h1 : (2 : ℤ_[2]) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  -- `⟨a, 2 b⟩ ≅ ⟨a + 2 b, 2 a b (a + 2 b)⟩` at the scale `2 ^ k`, in the basis `(1, 1)`,
  -- `(-2 b, a)`.
  have hfuse : (Matrix.toBilin' (Matrix.diagonal ![2 ^ k * a, 2 ^ (k + 1) * b])).Equivalent
      (Matrix.toBilin' (Matrix.diagonal
        ![2 ^ k * (a + 2 * b), 2 ^ (k + 1) * (a * b * (a + 2 * b))])) :=
    equivalent_toBilin'_diagonal_fin_two (x := 1) (y := 1) (z := -(2 * b)) (t := a)
      (by convert ha' using 1; ring) (by rw [h1]; ring) (by rw [h1]; ring) (by rw [h1]; ring)
  obtain ⟨z', hz', hspan⟩ := exists_span_range_eq_of_equivalent_toBilin' (B := B) (v := ![x, y])
    (fun i j ↦ by fin_cases i <;> fin_cases j <;> simp [hxx, hyy, hxy, hB.eq y x]) hfuse
  have hspan' : Submodule.span ℤ_[2] (Set.range ![z' 0] ∪ Set.range ![z' 1]) =
      Submodule.span ℤ_[2] (Set.range ![x] ∪ Set.range ![y]) := by
    rw [Matrix.range_cons_empty (z' 0), Matrix.range_cons_empty x, ← Matrix.range_cons,
      ← Matrix.range_cons, ← hspan, ← FinVec.etaExpand_eq z']
    rfl
  have hz'0 : B (z' 0) (z' 0) = 2 ^ k * (a + 2 * b) := by simpa using hz' 0 0
  have hz'1 : B (z' 1) (z' 1) = 2 ^ (k + 1) * (a * b * (a + 2 * b)) := by simpa using hz' 1 1
  obtain ⟨N', hN', hagree, ⟨m, t, G, hG, hGu, hvt, hv't, hNk, hN'k⟩,
    ⟨m', s, H, hH, hHu, hws, hw's, hNl, hN'l⟩⟩ :=
    h.exists_isJordanSplitting_of_span_eq hB h2 (k := k) (l := k + 1) (by omega) (v := ![x])
      (v' := ![z' 0]) (w := ![y]) (w' := ![z' 1]) (A := !![a]) (A' := !![a + 2 * b])
      (D := !![b]) (D' := !![a * b * (a + 2 * b)]) (fun i ↦ by fin_cases i; exact hx)
      (fun i ↦ by fin_cases i; exact hy)
      (fun i j ↦ by fin_cases i; fin_cases j; simpa using hxx)
      (fun i j ↦ by fin_cases i; fin_cases j; simpa using hz'0)
      (fun i j ↦ by fin_cases i; fin_cases j; simpa using hyy)
      (fun i j ↦ by fin_cases i; fin_cases j; simpa using hz'1)
      (by simpa using ha) (by simpa using ha') (by simpa using hb) (by simpa using hb')
      (fun i j ↦ by fin_cases i; fin_cases j; simpa using hz' 0 1) hspan'
  have hcA : IsSquare (c * (!![a] : Matrix (Fin 1) (Fin 1) ℤ_[2]).det * (!![a + 2 * b]).det) := by
    simpa [Matrix.det_fin_one_of, mul_assoc] using hc
  have hcD : IsSquare
      (c * (!![b] : Matrix (Fin 1) (Fin 1) ℤ_[2]).det * (!![a * b * (a + 2 * b)]).det) := by
    obtain ⟨r, hr⟩ := hc
    refine ⟨r * b, ?_⟩
    rw [Matrix.det_fin_one_of, Matrix.det_fin_one_of]
    linear_combination b ^ 2 * hr
  refine ⟨N', hN', hagree,
    fun n d d' ↦ isSquare_mul_det_mul_det_of_eq_span hB.isRefl (pow_mem h2 k)
      (A := !![a]) (A' := !![a + 2 * b]) (fun i j ↦ by fin_cases i; fin_cases j; simpa using hxx)
      (fun i j ↦ by fin_cases i; fin_cases j; simpa using hz'0) hG hvt hv't (by simpa using ha)
      (by simpa using ha') hGu hcA hNk hN'k d d',
    fun n d d' ↦ isSquare_mul_det_mul_det_of_eq_span hB.isRefl (pow_mem h2 (k + 1))
      (A := !![b]) (A' := !![a * b * (a + 2 * b)])
      (fun i j ↦ by fin_cases i; fin_cases j; simpa using hyy)
      (fun i j ↦ by fin_cases i; fin_cases j; simpa using hz'1) hH hws hw's (by simpa using hb)
      (by simpa using hb') hHu hcD hNl hN'l d d',
    fun C C' w w' hC hC' hw hw' ↦ ?_, fun C C' w w' hC hC' hw hw' ↦ ?_⟩
  · have := hB.eight_dvd_sub_sub_of_eq_span hxx hz'0 hG (fun j ↦ by simpa using hvt 0 j)
      (fun j ↦ by simpa using hv't 0 j) ha ha' hGu hNk hN'k hC hC' hw hw'
    rwa [add_sub_cancel_left] at this
  · have := hB.eight_dvd_sub_sub_of_eq_span hyy hz'1 hH (fun j ↦ by simpa using hws 0 j)
      (fun j ↦ by simpa using hw's 0 j) hb hb' hHu hNl hN'l hC hC' hw hw'
    convert dvd_add this (eight_dvd_mul_mul_add_two_mul_sub_sub ha hb) using 1
    ring

/-- **Oddity fusion between adjacent constituents of type I.** Let `N` be a Jordan splitting with
respect to `2` of a symmetric form `B` on a finite free `ℤ_[2]`-module, and let `x ∈ N k` and
`y ∈ N (k + 1)` with `B x x = 2 ^ k a` and `B y y = 2 ^ (k + 1) b` for units `a`, `b` with
`a + b ≡ 0` modulo `4`. Then `B` has a Jordan splitting `N'` agreeing with `N` away from `k` and
`k + 1`, in which the Gram determinants of the constituents of indices `k` and `k + 1` are
multiplied by `-1` up to squares, and the oddities of the unimodular rescalings of these
constituents change by `2 b` and `-2 b` modulo `8`. In the language of Conway–Sloane symbols, both
signs are kept and an oddity of `2 b` moves from the constituent of index `k + 1` to that of
index `k`. The underlying isometry is `⟨a, 2 b⟩ ≅ ⟨a + 2 b, 2 a b (a + 2 b)⟩`, for instance
`⟨1, 14⟩ ≅ ⟨15, 210⟩`, and `⟨15, 210⟩ ≅ ⟨7, 2⟩`. -/
theorem IsJordanSplitting.exists_oddityFusion_succ [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k : ℕ} {x y : M}
    (hx : x ∈ N k) (hy : y ∈ N (k + 1)) {a b : ℤ_[2]} (ha : IsUnit a) (hb : IsUnit b)
    (hxx : B x x = 2 ^ k * a) (hyy : B y y = 2 ^ (k + 1) * b) (hab : (4 : ℤ_[2]) ∣ a + b) :
    ∃ N' : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 N' ∧
      (∀ i, i ≠ k → i ≠ k + 1 → N' i = N i) ∧
      (∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N k)) (d' : Basis (Fin n) ℤ_[2] (N' k)),
        IsSquare (-((B.restrict (N k)).toMatrix d).det *
          ((B.restrict (N' k)).toMatrix d').det)) ∧
      (∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N (k + 1))) (d' : Basis (Fin n) ℤ_[2] (N' (k + 1))),
        IsSquare (-((B.restrict (N (k + 1))).toMatrix d).det *
          ((B.restrict (N' (k + 1))).toMatrix d').det)) ∧
      (∀ (C : BilinForm ℤ_[2] (N k)) (C' : BilinForm ℤ_[2] (N' k)) (w : N k) (w' : N' k),
        (2 : ℤ_[2]) ^ k • C = B.restrict (N k) → (2 : ℤ_[2]) ^ k • C' = B.restrict (N' k) →
        C.IsCharacteristic w → C'.IsCharacteristic w' → (8 : ℤ_[2]) ∣ C' w' w' - C w w - 2 * b) ∧
      ∀ (C : BilinForm ℤ_[2] (N (k + 1))) (C' : BilinForm ℤ_[2] (N' (k + 1))) (w : N (k + 1))
        (w' : N' (k + 1)), (2 : ℤ_[2]) ^ (k + 1) • C = B.restrict (N (k + 1)) →
        (2 : ℤ_[2]) ^ (k + 1) • C' = B.restrict (N' (k + 1)) →
        C.IsCharacteristic w → C'.IsCharacteristic w' → (8 : ℤ_[2]) ∣ C' w' w' - C w w + 2 * b := by
  obtain ⟨e, he⟩ := hab
  -- `-a (a + 2 b) = a (a - 8 e) ≡ 1` modulo `8`, so it is a square.
  have hc : IsSquare (-1 * a * (a + 2 * b)) := by
    refine isSquare_of_toZModPow_three_eq_one ?_
    rw [show -1 * a * (a + 2 * b) = a * (a - 8 * e) by linear_combination -2 * a * he]
    have hA := isUnit_iff_toZModPow_three_mul_self.mp ha
    simp only [map_mul, map_sub, map_ofNat]
    generalize toZModPow 3 a = A at hA ⊢
    generalize toZModPow 3 e = E
    revert A E
    decide
  obtain ⟨N', hN', hagree, hdk, hdl, hok, hol⟩ := h.exists_fusion_succ hB hx hy ha hb hxx hyy hc
  refine ⟨N', hN', hagree, fun n d d' ↦ by simpa using hdk n d d',
    fun n d d' ↦ by simpa using hdl n d d', hok, fun C C' w w' hC hC' hw hw' ↦ ?_⟩
  convert dvd_add (hol C C' w w' hC hC' hw hw') (dvd_mul_right 8 e) using 1
  linear_combination 2 * he

/-- **Sign walking between adjacent constituents of type I.** Let `N` be a Jordan splitting with
respect to `2` of a symmetric form `B` on a finite free `ℤ_[2]`-module, and let `x ∈ N k` and
`y ∈ N (k + 1)` with `B x x = 2 ^ k a` and `B y y = 2 ^ (k + 1) b` for units `a`, `b` with
`a ≡ b` modulo `4`. Then `B` has a Jordan splitting `N'` agreeing with `N` away from `k` and
`k + 1`, in which the Gram determinants of the constituents of indices `k` and `k + 1` are
multiplied by `3` up to squares, and the oddities of the unimodular rescalings of both constituents
change by `2 b` modulo `8`. In the language of Conway–Sloane symbols, both signs change and the
total oddity changes by `4`. The underlying isometry is `⟨a, 2 b⟩ ≅ ⟨a + 2 b, 2 a b (a + 2 b)⟩`, for
instance `⟨1, 2⟩ ≅ ⟨3, 6⟩`. -/
theorem IsJordanSplitting.exists_signWalk_succ_of_odd_of_odd [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k : ℕ} {x y : M}
    (hx : x ∈ N k) (hy : y ∈ N (k + 1)) {a b : ℤ_[2]} (ha : IsUnit a) (hb : IsUnit b)
    (hxx : B x x = 2 ^ k * a) (hyy : B y y = 2 ^ (k + 1) * b) (hab : (4 : ℤ_[2]) ∣ a - b) :
    ∃ N' : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 N' ∧
      (∀ i, i ≠ k → i ≠ k + 1 → N' i = N i) ∧
      (∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N k)) (d' : Basis (Fin n) ℤ_[2] (N' k)),
        IsSquare (3 * ((B.restrict (N k)).toMatrix d).det *
          ((B.restrict (N' k)).toMatrix d').det)) ∧
      (∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N (k + 1))) (d' : Basis (Fin n) ℤ_[2] (N' (k + 1))),
        IsSquare (3 * ((B.restrict (N (k + 1))).toMatrix d).det *
          ((B.restrict (N' (k + 1))).toMatrix d').det)) ∧
      (∀ (C : BilinForm ℤ_[2] (N k)) (C' : BilinForm ℤ_[2] (N' k)) (w : N k) (w' : N' k),
        (2 : ℤ_[2]) ^ k • C = B.restrict (N k) → (2 : ℤ_[2]) ^ k • C' = B.restrict (N' k) →
        C.IsCharacteristic w → C'.IsCharacteristic w' → (8 : ℤ_[2]) ∣ C' w' w' - C w w - 2 * b) ∧
      ∀ (C : BilinForm ℤ_[2] (N (k + 1))) (C' : BilinForm ℤ_[2] (N' (k + 1))) (w : N (k + 1))
        (w' : N' (k + 1)), (2 : ℤ_[2]) ^ (k + 1) • C = B.restrict (N (k + 1)) →
        (2 : ℤ_[2]) ^ (k + 1) • C' = B.restrict (N' (k + 1)) →
        C.IsCharacteristic w → C'.IsCharacteristic w' → (8 : ℤ_[2]) ∣ C' w' w' - C w w - 2 * b := by
  obtain ⟨e, he⟩ := hab
  -- `3 a (a + 2 b) = 3 a (3 a - 8 e) ≡ 9 a ^ 2 ≡ 1` modulo `8`, so it is a square.
  have hc : IsSquare (3 * a * (a + 2 * b)) := by
    refine isSquare_of_toZModPow_three_eq_one ?_
    rw [show 3 * a * (a + 2 * b) = 3 * a * (3 * a - 8 * e) by linear_combination -6 * a * he]
    have hA := isUnit_iff_toZModPow_three_mul_self.mp ha
    simp only [map_mul, map_sub, map_ofNat]
    generalize toZModPow 3 a = A at hA ⊢
    generalize toZModPow 3 e = E
    revert A E
    decide
  obtain ⟨N', hN', hagree, hdk, hdl, hok, hol⟩ := h.exists_fusion_succ hB hx hy ha hb hxx hyy hc
  refine ⟨N', hN', hagree, hdk, hdl, hok, fun C C' w w' hC hC' hw hw' ↦ ?_⟩
  convert dvd_add (hol C C' w w' hC hC' hw hw') (dvd_mul_right 8 e) using 1
  linear_combination 2 * he

end LinearMap.BilinForm
