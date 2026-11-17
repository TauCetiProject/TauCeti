/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.CappedReflection
public import TauCeti.RepresentationTheory.LSPath.Subdivision
public import TauCeti.RepresentationTheory.LSPath.Word

/-!
# Word-level dilation similarity and stretched Lakshmibai–Seshadri paths

From the single-root dilation similarity identities in
`TauCeti.RepresentationTheory.LSPath.CappedReflection` (`PLPath.lowerIter_map_smul` and
`PLPath.raiseIter_map_smul`), this file deduces word-level dilation similarity on piecewise-linear
paths without any integrality assumption: for any `0 < a` in `𝕜` and natural numbers `m, n` with
`(m : 𝕜) = a * n`, applying a lowering or raising word replicated `m` times per letter on the
`a`-dilated path equals the `a`-dilation of applying the word replicated `n` times per letter on
the original path (`PLPath.lowerWord_flatMap_replicate_map_smul`,
`PLPath.raiseWord_flatMap_replicate_map_smul`).

Specializing to `a = (n : 𝕜)` (`0 < n`) intertwines each root word `w` on `π` with the
letter-replicated word `w.flatMap (List.replicate n)` on the `n`-dilated path, while
`a = (n : 𝕜)⁻¹` recovers the fractional-contraction identity intertwining `w` on `(n : 𝕜)⁻¹ • π`
with `w.flatMap (List.replicate n)` on `π`.

Applied to `LSPath.stretch` and `LSPath.subdivisionWord`, stretching a Lakshmibai–Seshadri path by
`n` (and, when `n` clears segment durations, realizing it as a concatenation of `n` straight
Weyl-orbit paths) intertwines root operators and words on the original realization with `n`-fold
iterated operators and letter-replicated words on the stretched realization.

## Main results

* `TauCeti.PLPath.lowerWord_flatMap_replicate_map_smul`,
  `TauCeti.PLPath.raiseWord_flatMap_replicate_map_smul`: general positive-scalar word similarity
  when `(m : 𝕜) = a * n`.
* `TauCeti.PLPath.lowerWord_flatMap_replicate_map_natCast_smul`,
  `TauCeti.PLPath.raiseWord_flatMap_replicate_map_natCast_smul`: word-level similarity under
  positive-integer dilation.
* `TauCeti.PLPath.lowerWord_map_inv_natCast_smul`,
  `TauCeti.PLPath.raiseWord_map_inv_natCast_smul`: word-level similarity under fractional
  `(n : 𝕜)⁻¹` contraction.
* `TauCeti.LSPath.lowerIter_toPLPath_stretch`, `TauCeti.LSPath.raiseIter_toPLPath_stretch`,
  `TauCeti.LSPath.lowerWord_flatMap_replicate_prod_subdivisionWord`,
  `TauCeti.LSPath.raiseWord_flatMap_replicate_prod_subdivisionWord`: intertwining `LSPath.stretch`
  and integral straight-path subdivisions with iterated root operators and letter-replicated words.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§1–2, 5 (Lemma 2.1(d) and Theorem 5.1).
-/

public section

namespace TauCeti.PLPath

open Module

variable {ι 𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-! ### Word-level similarity on piecewise-linear paths -/

section Words

variable {F : ι → Dual 𝕜 V} {x : ι → V}

/-- **Dilation similarity for lowering words**: for `F i (x i) = 2`, `0 < a`, and
`(m : 𝕜) = a * n`, lowering along `w.flatMap (List.replicate m)` on the `a`-dilated path equals
the `a`-dilation of lowering along `w.flatMap (List.replicate n)` on the original path. -/
theorem lowerWord_flatMap_replicate_map_smul (hx : ∀ i, F i (x i) = 2) {a : 𝕜} (ha : 0 < a)
    {m n : ℕ} (hmn : (m : 𝕜) = a * n) (w : List ι) (π : PLPath 𝕜 V) :
    lowerWord F x (w.flatMap (List.replicate m)) (π.map (a • LinearMap.id)) =
      (lowerWord F x (w.flatMap (List.replicate n)) π).map
        (fun ρ ↦ ρ.map (a • LinearMap.id)) := by
  induction w generalizing π with
  | nil => simp
  | cons i w ih =>
    rw [List.flatMap_cons, lowerWord_append, lowerWord_replicate,
      lowerIter_map_smul (hx i) ha hmn, List.flatMap_cons, lowerWord_append, lowerWord_replicate]
    cases lowerIter (F i) (x i) n π <;> simp [ih]

/-- **Dilation similarity for raising words**: for `F i (x i) = 2`, `0 < a`, and
`(m : 𝕜) = a * n`, raising along `w.flatMap (List.replicate m)` on the `a`-dilated path equals the
`a`-dilation of raising along `w.flatMap (List.replicate n)` on the original path. -/
theorem raiseWord_flatMap_replicate_map_smul (hx : ∀ i, F i (x i) = 2) {a : 𝕜} (ha : 0 < a)
    {m n : ℕ} (hmn : (m : 𝕜) = a * n) (w : List ι) (π : PLPath 𝕜 V) :
    raiseWord F x (w.flatMap (List.replicate m)) (π.map (a • LinearMap.id)) =
      (raiseWord F x (w.flatMap (List.replicate n)) π).map
        (fun ρ ↦ ρ.map (a • LinearMap.id)) := by
  rw [raiseWord_eq_map_lowerWord_reverse, raiseWord_eq_map_lowerWord_reverse, ← map_reverse,
    lowerWord_flatMap_replicate_map_smul hx ha hmn, Option.map_map, Option.map_map]
  congr 1
  funext ρ
  exact (map_reverse ρ (a • LinearMap.id)).symm

private theorem flatMap_replicate_one {α : Type*} (w : List α) :
    w.flatMap (List.replicate 1) = w := by
  induction w with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Lowering along the `n`-fold letter-replicated word on an `n`-dilated path equals the
`n`-dilation of lowering along the original word. -/
theorem lowerWord_flatMap_replicate_map_natCast_smul (hx : ∀ i, F i (x i) = 2) {n : ℕ}
    (hn : 0 < n) (w : List ι) (π : PLPath 𝕜 V) :
    lowerWord F x (w.flatMap (List.replicate n)) (π.map ((n : 𝕜) • LinearMap.id)) =
      (lowerWord F x w π).map (fun ρ ↦ ρ.map ((n : 𝕜) • LinearMap.id)) := by
  simpa only [flatMap_replicate_one] using
    lowerWord_flatMap_replicate_map_smul hx (Nat.cast_pos.mpr hn) (m := n) (n := 1) (by simp) w π

/-- Raising along the `n`-fold letter-replicated word on an `n`-dilated path equals the
`n`-dilation of raising along the original word. -/
theorem raiseWord_flatMap_replicate_map_natCast_smul (hx : ∀ i, F i (x i) = 2) {n : ℕ}
    (hn : 0 < n) (w : List ι) (π : PLPath 𝕜 V) :
    raiseWord F x (w.flatMap (List.replicate n)) (π.map ((n : 𝕜) • LinearMap.id)) =
      (raiseWord F x w π).map (fun ρ ↦ ρ.map ((n : 𝕜) • LinearMap.id)) := by
  simpa only [flatMap_replicate_one] using
    raiseWord_flatMap_replicate_map_smul hx (Nat.cast_pos.mpr hn) (m := n) (n := 1) (by simp) w π

/-- Lowering along `w` on the contracted path `(n : 𝕜)⁻¹ • π` equals contracting lowering along the
`n`-fold letter-replicated word on `π`. -/
theorem lowerWord_map_inv_natCast_smul (hx : ∀ i, F i (x i) = 2) {n : ℕ} (hn : 0 < n)
    (w : List ι) (π : PLPath 𝕜 V) :
    lowerWord F x w (π.map ((n : 𝕜)⁻¹ • LinearMap.id)) =
      (lowerWord F x (w.flatMap (List.replicate n)) π).map
        (fun ρ ↦ ρ.map ((n : 𝕜)⁻¹ • LinearMap.id)) := by
  have hn0 : (n : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simpa only [flatMap_replicate_one] using
    lowerWord_flatMap_replicate_map_smul hx (inv_pos.mpr (Nat.cast_pos.mpr hn))
      (m := 1) (n := n) (Nat.cast_one.trans (inv_mul_cancel₀ hn0).symm) w π

/-- Raising along `w` on the contracted path `(n : 𝕜)⁻¹ • π` equals contracting raising along the
`n`-fold letter-replicated word on `π`. -/
theorem raiseWord_map_inv_natCast_smul (hx : ∀ i, F i (x i) = 2) {n : ℕ} (hn : 0 < n)
    (w : List ι) (π : PLPath 𝕜 V) :
    raiseWord F x w (π.map ((n : 𝕜)⁻¹ • LinearMap.id)) =
      (raiseWord F x (w.flatMap (List.replicate n)) π).map
        (fun ρ ↦ ρ.map ((n : 𝕜)⁻¹ • LinearMap.id)) := by
  have hn0 : (n : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simpa only [flatMap_replicate_one] using
    raiseWord_flatMap_replicate_map_smul hx (inv_pos.mpr (Nat.cast_pos.mpr hn))
      (m := 1) (n := n) (Nat.cast_one.trans (inv_mul_cancel₀ hn0).symm) w π

end Words

end TauCeti.PLPath

namespace TauCeti.LSPath

open Module RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}
  (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] (f : M →+ V)

/-- Stretching an LS path by `n` multiplies every linear-form minimum height of its realization by
`n`. -/
@[simp]
theorem minHeight_toPLPath_stretch (π : LSPath P b lam) (n : ℕ) (hn : 0 < n) (g : Dual 𝕜 V) :
    ((π.stretch n hn).toPLPath 𝕜 f).minHeight g = (n : 𝕜) * (π.toPLPath 𝕜 f).minHeight g := by
  rw [toPLPath_stretch, PLPath.minHeight_map_smul (Nat.cast_nonneg n)]

/-- Stretching an LS path by `n` intertwines single lowering on `π.toPLPath 𝕜 f` with `n`-fold
lowering on `(π.stretch n hn).toPLPath 𝕜 f`. -/
theorem lowerIter_toPLPath_stretch (π : LSPath P b lam) {g : Dual 𝕜 V} {x : V} (hx : g x = 2)
    {n : ℕ} (hn : 0 < n) :
    PLPath.lowerIter g x n ((π.stretch n hn).toPLPath 𝕜 f) =
      (PLPath.lower g x (π.toPLPath 𝕜 f)).map (fun q ↦ q.map ((n : 𝕜) • LinearMap.id)) := by
  rw [toPLPath_stretch, PLPath.lowerIter_map_natCast_smul hx hn]

/-- Stretching an LS path by `n` intertwines single raising on `π.toPLPath 𝕜 f` with `n`-fold
raising on `(π.stretch n hn).toPLPath 𝕜 f`. -/
theorem raiseIter_toPLPath_stretch (π : LSPath P b lam) {g : Dual 𝕜 V} {x : V} (hx : g x = 2)
    {n : ℕ} (hn : 0 < n) :
    PLPath.raiseIter g x n ((π.stretch n hn).toPLPath 𝕜 f) =
      (PLPath.raise g x (π.toPLPath 𝕜 f)).map (fun q ↦ q.map ((n : 𝕜) • LinearMap.id)) := by
  rw [toPLPath_stretch, PLPath.raiseIter_map_natCast_smul hx hn]

/-- Stretching an LS path by `n` intertwines lowering words on `π.toPLPath 𝕜 f` with `n`-fold
letter-replicated lowering words on `(π.stretch n hn).toPLPath 𝕜 f`. -/
theorem lowerWord_flatMap_replicate_toPLPath_stretch (π : LSPath P b lam) {α : Type*}
    {F : α → Dual 𝕜 V} {x : α → V} (hx : ∀ a, F a (x a) = 2) {n : ℕ} (hn : 0 < n)
    (w : List α) :
    PLPath.lowerWord F x (w.flatMap (List.replicate n)) ((π.stretch n hn).toPLPath 𝕜 f) =
      (PLPath.lowerWord F x w (π.toPLPath 𝕜 f)).map (fun ρ ↦ ρ.map ((n : 𝕜) • LinearMap.id)) := by
  rw [toPLPath_stretch, PLPath.lowerWord_flatMap_replicate_map_natCast_smul hx hn]

/-- Stretching an LS path by `n` intertwines raising words on `π.toPLPath 𝕜 f` with `n`-fold
letter-replicated raising words on `(π.stretch n hn).toPLPath 𝕜 f`. -/
theorem raiseWord_flatMap_replicate_toPLPath_stretch (π : LSPath P b lam) {α : Type*}
    {F : α → Dual 𝕜 V} {x : α → V} (hx : ∀ a, F a (x a) = 2) {n : ℕ} (hn : 0 < n)
    (w : List α) :
    PLPath.raiseWord F x (w.flatMap (List.replicate n)) ((π.stretch n hn).toPLPath 𝕜 f) =
      (PLPath.raiseWord F x w (π.toPLPath 𝕜 f)).map (fun ρ ↦ ρ.map ((n : 𝕜) • LinearMap.id)) := by
  rw [toPLPath_stretch, PLPath.raiseWord_flatMap_replicate_map_natCast_smul hx hn]

/-- When `n` clears the segment durations of `π`, lowering along `w.flatMap (List.replicate n)` on
the straight-orbit-path concatenation of `π.subdivisionWord m` equals the `n`-dilation of lowering
along `w` on `π.toPLPath 𝕜 f`. -/
theorem lowerWord_flatMap_replicate_prod_subdivisionWord (π : LSPath P b lam) {α : Type*}
    {F : α → Dual 𝕜 V} {x : α → V} (hx : ∀ a, F a (x a) = 2) {n : ℕ} (hn : 0 < n)
    (m : Fin (π.length + 1) → ℕ) (hm : ∀ j, (m j : ℚ) = (n : ℚ) * π.duration j) (w : List α) :
    PLPath.lowerWord F x (w.flatMap (List.replicate n))
        (((π.subdivisionWord m).map fun σ ↦ PLPath.straight 𝕜 (f (σ • lam))).prod) =
      (PLPath.lowerWord F x w (π.toPLPath 𝕜 f)).map
        (fun ρ ↦ ρ.map ((n : 𝕜) • LinearMap.id)) := by
  rw [← π.toPLPath_stretch_eq_prod_subdivisionWord 𝕜 f n hn m hm,
    π.lowerWord_flatMap_replicate_toPLPath_stretch 𝕜 f hx hn w]

/-- When `n` clears the segment durations of `π`, raising along `w.flatMap (List.replicate n)` on
the straight-orbit-path concatenation of `π.subdivisionWord m` equals the `n`-dilation of raising
along `w` on `π.toPLPath 𝕜 f`. -/
theorem raiseWord_flatMap_replicate_prod_subdivisionWord (π : LSPath P b lam) {α : Type*}
    {F : α → Dual 𝕜 V} {x : α → V} (hx : ∀ a, F a (x a) = 2) {n : ℕ} (hn : 0 < n)
    (m : Fin (π.length + 1) → ℕ) (hm : ∀ j, (m j : ℚ) = (n : ℚ) * π.duration j) (w : List α) :
    PLPath.raiseWord F x (w.flatMap (List.replicate n))
        (((π.subdivisionWord m).map fun σ ↦ PLPath.straight 𝕜 (f (σ • lam))).prod) =
      (PLPath.raiseWord F x w (π.toPLPath 𝕜 f)).map
        (fun ρ ↦ ρ.map ((n : 𝕜) • LinearMap.id)) := by
  rw [← π.toPLPath_stretch_eq_prod_subdivisionWord 𝕜 f n hn m hm,
    π.raiseWord_flatMap_replicate_toPLPath_stretch 𝕜 f hx hn w]

end TauCeti.LSPath
