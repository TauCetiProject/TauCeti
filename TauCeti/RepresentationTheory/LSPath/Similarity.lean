/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.CappedReflection
public import TauCeti.RepresentationTheory.LSPath.StringLength
public import TauCeti.RepresentationTheory.LSPath.Subdivision
public import TauCeti.RepresentationTheory.LSPath.Word

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Iterated root operators as capped reflections and similarity under dilation

Fix a vector `x : V` and a linear form `f : Dual 𝕜 V` with `f x = 2`. Combining the single-step
formula `PLPath.lower_eq_some_cappedReflection` with the composition theorem
`PLPath.cappedReflection_cappedReflection` identifies every iterate `PLPath.lowerIter f x n p` with
a single capped reflection at `p.minHeight f + n` when `(n : 𝕜) ≤ f p.endpoint - p.minHeight f`,
and `none` otherwise.

Because positive dilation commutes with `cappedReflection` after scaling the cap
(`PLPath.cappedReflection_map_smul`), this yields Littelmann's dilation-similarity identities
without any integrality assumption on the path: for any `0 < a` in `𝕜` and natural numbers `m, n`
with `(m : 𝕜) = a * n`, `lowerIter f x m` and `raiseIter f x m` on the `a`-dilated path equal the
`a`-dilation of `lowerIter f x n` and `raiseIter f x n` on the original path. Specializing to
`a = n` (`0 < n`) intertwines each single root operator with its `n`-fold iterate and each root
word `w` with the letter-replicated word `w.flatMap (List.replicate n)`, while `a = (n : 𝕜)⁻¹`
recovers Littelmann's fractional-contraction formula.

Applied to `LSPath.stretch` and `LSPath.subdivisionWord`, stretching a Lakshmibai–Seshadri path by
`n` (and, when `n` clears segment durations, realizing it as a concatenation of `n` straight
Weyl-orbit paths) intertwines root operators and words on the original realization with `n`-fold
iterated operators and letter-replicated words on the stretched realization.

## Main results

* `TauCeti.PLPath.lowerIter_eq_some_cappedReflection`,
  `TauCeti.PLPath.lowerIter_eq_ite_cappedReflection`: `n`-fold lowering is capped reflection at
  `p.minHeight f + n`.
* `TauCeti.PLPath.lowerIter_map_smul`, `TauCeti.PLPath.raiseIter_map_smul`: general positive-scalar
  similarity when `(m : 𝕜) = a * n`, with positive-integer dilation and fractional-contraction
  specializations.
* `TauCeti.PLPath.lowerWord_flatMap_replicate_map_natCast_smul`,
  `TauCeti.PLPath.raiseWord_flatMap_replicate_map_natCast_smul`: word-level similarity under
  positive-integer dilation and contraction.
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

section IteratedCappedReflection

variable {f : Dual 𝕜 V} {x : V}

/-- For `f x = 2`, applying `lower f x` `n` times is capped reflection at `p.minHeight f + n`,
whenever `(n : 𝕜) ≤ f p.endpoint - p.minHeight f`. -/
theorem lowerIter_eq_some_cappedReflection (hx : f x = 2) {n : ℕ} (p : PLPath 𝕜 V)
    (hp : (n : 𝕜) ≤ f p.endpoint - p.minHeight f) :
    lowerIter f x n p = some (cappedReflection f x (p.minHeight f + n) p) := by
  induction n generalizing p with
  | zero =>
    simp
  | succ n ih =>
    have hp₁ : 1 ≤ f p.endpoint - p.minHeight f := by
      push_cast at hp
      linarith [Nat.cast_nonneg (α := 𝕜) n]
    have hlow := lower_eq_some_cappedReflection (x := x) p hp₁
    set q := cappedReflection f x (p.minHeight f + 1) p
    have hqn : (n : 𝕜) ≤ f q.endpoint - q.minHeight f := by
      have hstep := apply_endpoint_sub_minHeight_of_lower_eq_some hx hlow
      push_cast at hp
      linarith
    rw [lowerIter_succ, hlow, Option.bind_some, ih q hqn,
      cappedReflection_minHeight_add hx zero_le_one (Nat.cast_nonneg n) p hp₁]
    congr 2
    push_cast
    ring

/-- Closed-form description of `n`-fold lowering as a single capped reflection. -/
theorem lowerIter_eq_ite_cappedReflection (hx : f x = 2) (n : ℕ) (p : PLPath 𝕜 V) :
    lowerIter f x n p =
      if (n : 𝕜) ≤ f p.endpoint - p.minHeight f then
        some (cappedReflection f x (p.minHeight f + n) p)
      else none := by
  split_ifs with hp
  · exact lowerIter_eq_some_cappedReflection hx p hp
  · exact (lowerIter_eq_none_iff hx).mpr (lt_of_not_ge hp)

/-! ### Similarity of root operators under positive dilation -/

/-- **Dilation similarity for iterated lowering** (Littelmann): for `f x = 2`, `0 < a`, and
`(m : 𝕜) = a * n`, `m`-fold lowering on the `a`-dilated path equals the `a`-dilation of `n`-fold
lowering on the original path. No integrality of the path is needed. -/
theorem lowerIter_map_smul (hx : f x = 2) {a : 𝕜} (ha : 0 < a) {m n : ℕ}
    (hmn : (m : 𝕜) = a * n) (p : PLPath 𝕜 V) :
    lowerIter f x m (p.map (a • LinearMap.id)) =
      (lowerIter f x n p).map (fun q ↦ q.map (a • LinearMap.id)) := by
  have hdiff :
      f (p.map (a • LinearMap.id)).endpoint - (p.map (a • LinearMap.id)).minHeight f =
        a * (f p.endpoint - p.minHeight f) := by
    rw [endpoint_map, LinearMap.smul_apply, LinearMap.id_apply, map_smul, smul_eq_mul,
      minHeight_map_smul ha.le, mul_sub]
  have hcond :
      ((m : 𝕜) ≤
          f (p.map (a • LinearMap.id)).endpoint - (p.map (a • LinearMap.id)).minHeight f) ↔
        (n : 𝕜) ≤ f p.endpoint - p.minHeight f := by
    rw [hdiff, hmn, mul_le_mul_iff_right₀ ha]
  rw [lowerIter_eq_ite_cappedReflection hx, lowerIter_eq_ite_cappedReflection hx]
  by_cases hn : (n : 𝕜) ≤ f p.endpoint - p.minHeight f
  · rw [ite_eq_left (hcond.mpr hn), ite_eq_left hn, Option.map_some, minHeight_map_smul ha.le,
      hmn, ← mul_add, cappedReflection_map_smul ha]
  · rw [ite_eq_right (mt hcond.mp hn), ite_eq_right hn, Option.map_none]

/-- **Dilation similarity for iterated raising** (Littelmann): for `f x = 2`, `0 < a`, and
`(m : 𝕜) = a * n`, `m`-fold raising on the `a`-dilated path equals the `a`-dilation of `n`-fold
raising on the original path. -/
theorem raiseIter_map_smul (hx : f x = 2) {a : 𝕜} (ha : 0 < a) {m n : ℕ}
    (hmn : (m : 𝕜) = a * n) (p : PLPath 𝕜 V) :
    raiseIter f x m (p.map (a • LinearMap.id)) =
      (raiseIter f x n p).map (fun q ↦ q.map (a • LinearMap.id)) := by
  rw [raiseIter_eq_map_lowerIter_reverse, raiseIter_eq_map_lowerIter_reverse, ← map_reverse,
    lowerIter_map_smul hx ha hmn, Option.map_map, Option.map_map]
  congr 1
  funext q
  exact (map_reverse q (a • LinearMap.id)).symm

/-- For `0 < n`, lowering `k * n` times on the `n`-dilated path equals the `n`-dilation of
lowering `k` times on the original path. -/
theorem lowerIter_mul_map_natCast_smul (hx : f x = 2) (k : ℕ) {n : ℕ} (hn : 0 < n)
    (p : PLPath 𝕜 V) :
    lowerIter f x (k * n) (p.map ((n : 𝕜) • LinearMap.id)) =
      (lowerIter f x k p).map (fun q ↦ q.map ((n : 𝕜) • LinearMap.id)) :=
  lowerIter_map_smul hx (Nat.cast_pos.mpr hn) (by push_cast; ring) p

/-- For `0 < n`, raising `k * n` times on the `n`-dilated path equals the `n`-dilation of raising
`k` times on the original path. -/
theorem raiseIter_mul_map_natCast_smul (hx : f x = 2) (k : ℕ) {n : ℕ} (hn : 0 < n)
    (p : PLPath 𝕜 V) :
    raiseIter f x (k * n) (p.map ((n : 𝕜) • LinearMap.id)) =
      (raiseIter f x k p).map (fun q ↦ q.map ((n : 𝕜) • LinearMap.id)) :=
  raiseIter_map_smul hx (Nat.cast_pos.mpr hn) (by push_cast; ring) p

/-- Lowering `n` times (`0 < n`) on the `n`-dilated path equals the `n`-dilation of lowering once
on the original path. -/
theorem lowerIter_map_natCast_smul (hx : f x = 2) {n : ℕ} (hn : 0 < n) (p : PLPath 𝕜 V) :
    lowerIter f x n (p.map ((n : 𝕜) • LinearMap.id)) =
      (lower f x p).map (fun q ↦ q.map ((n : 𝕜) • LinearMap.id)) := by
  simpa using lowerIter_mul_map_natCast_smul hx 1 hn p

/-- Raising `n` times (`0 < n`) on the `n`-dilated path equals the `n`-dilation of raising once on
the original path. -/
theorem raiseIter_map_natCast_smul (hx : f x = 2) {n : ℕ} (hn : 0 < n) (p : PLPath 𝕜 V) :
    raiseIter f x n (p.map ((n : 𝕜) • LinearMap.id)) =
      (raise f x p).map (fun q ↦ q.map ((n : 𝕜) • LinearMap.id)) := by
  simpa using raiseIter_mul_map_natCast_smul hx 1 hn p

/-- Fractional contraction form of similarity (Littelmann, Lemma 2.1(d)): for `0 < n`, lowering
once on `(n : 𝕜)⁻¹ • p` equals contracting `n`-fold lowering on `p`. -/
theorem lower_map_inv_natCast_smul (hx : f x = 2) {n : ℕ} (hn : 0 < n) (p : PLPath 𝕜 V) :
    lower f x (p.map ((n : 𝕜)⁻¹ • LinearMap.id)) =
      (lowerIter f x n p).map (fun q ↦ q.map ((n : 𝕜)⁻¹ • LinearMap.id)) := by
  have hn0 : (n : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simpa using lowerIter_map_smul hx (inv_pos.mpr (Nat.cast_pos.mpr hn))
    (m := 1) (n := n) (Nat.cast_one.trans (inv_mul_cancel₀ hn0).symm) p

/-- Fractional contraction form of similarity for raising: for `0 < n`, raising once on
`(n : 𝕜)⁻¹ • p` equals contracting `n`-fold raising on `p`. -/
theorem raise_map_inv_natCast_smul (hx : f x = 2) {n : ℕ} (hn : 0 < n) (p : PLPath 𝕜 V) :
    raise f x (p.map ((n : 𝕜)⁻¹ • LinearMap.id)) =
      (raiseIter f x n p).map (fun q ↦ q.map ((n : 𝕜)⁻¹ • LinearMap.id)) := by
  have hn0 : (n : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simpa using raiseIter_map_smul hx (inv_pos.mpr (Nat.cast_pos.mpr hn))
    (m := 1) (n := n) (Nat.cast_one.trans (inv_mul_cancel₀ hn0).symm) p

end IteratedCappedReflection

/-! ### Word-level similarity on piecewise-linear paths -/

section Words

variable {F : ι → Dual 𝕜 V} {x : ι → V}

/-- Lowering along `n` copies of `i` is `lowerIter (F i) (x i) n`. -/
@[simp]
theorem lowerWord_replicate (n : ℕ) (i : ι) (π : PLPath 𝕜 V) :
    lowerWord F x (List.replicate n i) π = lowerIter (F i) (x i) n π := by
  induction n generalizing π with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, lowerWord_cons, lowerIter_succ]
    cases lower (F i) (x i) π <;> simp [ih]

/-- Raising along `n` copies of `i` is `raiseIter (F i) (x i) n`. -/
@[simp]
theorem raiseWord_replicate (n : ℕ) (i : ι) (π : PLPath 𝕜 V) :
    raiseWord F x (List.replicate n i) π = raiseIter (F i) (x i) n π := by
  induction n generalizing π with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, raiseWord_cons, raiseIter_succ]
    cases raise (F i) (x i) π <;> simp [ih]

/-- Lowering along the `n`-fold letter-replicated word on an `n`-dilated path equals the
`n`-dilation of lowering along the original word. -/
theorem lowerWord_flatMap_replicate_map_natCast_smul (hx : ∀ i, F i (x i) = 2) {n : ℕ}
    (hn : 0 < n) (w : List ι) (π : PLPath 𝕜 V) :
    lowerWord F x (w.flatMap (List.replicate n)) (π.map ((n : 𝕜) • LinearMap.id)) =
      (lowerWord F x w π).map (fun ρ ↦ ρ.map ((n : 𝕜) • LinearMap.id)) := by
  induction w generalizing π with
  | nil => simp
  | cons i w ih =>
    rw [List.flatMap_cons, lowerWord_append, lowerWord_replicate,
      lowerIter_map_natCast_smul (hx i) hn, lowerWord_cons]
    cases lower (F i) (x i) π <;> simp [ih]

/-- Raising along the `n`-fold letter-replicated word on an `n`-dilated path equals the
`n`-dilation of raising along the original word. -/
theorem raiseWord_flatMap_replicate_map_natCast_smul (hx : ∀ i, F i (x i) = 2) {n : ℕ}
    (hn : 0 < n) (w : List ι) (π : PLPath 𝕜 V) :
    raiseWord F x (w.flatMap (List.replicate n)) (π.map ((n : 𝕜) • LinearMap.id)) =
      (raiseWord F x w π).map (fun ρ ↦ ρ.map ((n : 𝕜) • LinearMap.id)) := by
  induction w generalizing π with
  | nil => simp
  | cons i w ih =>
    rw [List.flatMap_cons, raiseWord_append, raiseWord_replicate,
      raiseIter_map_natCast_smul (hx i) hn, raiseWord_cons]
    cases raise (F i) (x i) π <;> simp [ih]

/-- Lowering along `w` on the contracted path `(n : 𝕜)⁻¹ • π` equals contracting lowering along the
`n`-fold letter-replicated word on `π`. -/
theorem lowerWord_map_inv_natCast_smul (hx : ∀ i, F i (x i) = 2) {n : ℕ} (hn : 0 < n)
    (w : List ι) (π : PLPath 𝕜 V) :
    lowerWord F x w (π.map ((n : 𝕜)⁻¹ • LinearMap.id)) =
      (lowerWord F x (w.flatMap (List.replicate n)) π).map
        (fun ρ ↦ ρ.map ((n : 𝕜)⁻¹ • LinearMap.id)) := by
  induction w generalizing π with
  | nil => simp
  | cons i w ih =>
    rw [lowerWord_cons, lower_map_inv_natCast_smul (hx i) hn, List.flatMap_cons, lowerWord_append,
      lowerWord_replicate]
    cases lowerIter (F i) (x i) n π <;> simp [ih]

/-- Raising along `w` on the contracted path `(n : 𝕜)⁻¹ • π` equals contracting raising along the
`n`-fold letter-replicated word on `π`. -/
theorem raiseWord_map_inv_natCast_smul (hx : ∀ i, F i (x i) = 2) {n : ℕ} (hn : 0 < n)
    (w : List ι) (π : PLPath 𝕜 V) :
    raiseWord F x w (π.map ((n : 𝕜)⁻¹ • LinearMap.id)) =
      (raiseWord F x (w.flatMap (List.replicate n)) π).map
        (fun ρ ↦ ρ.map ((n : 𝕜)⁻¹ • LinearMap.id)) := by
  induction w generalizing π with
  | nil => simp
  | cons i w ih =>
    rw [raiseWord_cons, raise_map_inv_natCast_smul (hx i) hn, List.flatMap_cons, raiseWord_append,
      raiseWord_replicate]
    cases raiseIter (F i) (x i) n π <;> simp [ih]

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
