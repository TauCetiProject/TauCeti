/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Valuation.ColengthDvd
import TauCeti.LinearAlgebra.Matrix.Divisibility

/-!
# Congruences for paired theta directions

A block of directions of height one is distinguished at each end of a pairing. To make
Frobenius-twisted pairings vanish modulo a scalar, one can scale a whole block or impose one
linear congruence against a distinguished direction. These options have different costs on
the two sides: the Frobenius allows the left modulus to be a root of the right modulus.
The colengths record these costs before passing to valuations and allow constraints from
several partners to be imposed on the same directions.

The allocation follows `New.exists_congruenceChoice_cost_eq_and_covers` and
`New.exists_newDirection_dvd` in `grh/src/New/Derivatives/Divisibility/NullFrames.lean`
of [grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
-/

public section

open Finset Matrix Pointwise

namespace TauCeti

variable {R ι n : Type*} [CommRing R]

section LocalConstraints

variable [PreValuationRing R]

/-- One linear congruence costs one power of the modulus; requiring all coordinates to be
multiples of the modulus costs one power per coordinate. Both may be imposed together. -/
private theorem directionConstraints (k : ℕ) (d : R) (f : (Fin k → R) →ₗ[R] R)
    (scale test : Prop) [Decidable scale] [Decidable test] :
    let M := if scale then d • (⊤ : Submodule R (Fin k → R)) else ⊤
    let N := if test then Submodule.comap f (Ideal.span {d}) else ⊤
    (⊤ : Submodule R (Fin k → R)).ColengthDvd (M ⊓ N)
      (d ^ ((if scale then k else 0) + (if test then 1 else 0))) := by
  intro M N
  have hM : (⊤ : Submodule R (Fin k → R)).ColengthDvd M (d ^ (if scale then k else 0)) := by
    by_cases hs : scale
    · simpa [M, hs] using Submodule.colengthDvd_top_smul_top (ι := Fin k) d
    · simp [M, hs]
  have hN : M.ColengthDvd (M ⊓ N) (d ^ (if test then 1 else 0)) := by
    by_cases ht : test
    · simpa [N, ht] using Submodule.colengthDvd_inf_comap_span M f d
    · simp [N, ht]
  rw [pow_add]
  exact hM.trans hN

end LocalConstraints

section PairedDirections

variable [Fintype n] {height : ι → ℕ}

/-- The distinguished block has one coordinate; other block sizes are given by `height`. -/
private abbrev directionBlockSize (height : ι → ℕ) (h : Option ι) : ℕ := h.elim 1 height

/-- Divisibility in a paired block follows from scaling either argument, or from one
linear test when the opposite argument comes from the distinguished block. -/
private theorem dvd_of_direction_cover {p e : ℕ} (hp : p.Prime) {d : R}
    (hd : d ^ (p ^ e) ∣ (p : R))
    (Y Z : ∀ h : Option ι, (Fin (directionBlockSize height h) → R) →ₗ[R] (n → R))
    (root : n → R) (hroot : ∀ i, root i ^ (p ^ e) = Z none 1 i)
    {h j : Option ι} (x : Fin (directionBlockSize height h) → R)
    (y : Fin (directionBlockSize height j) → R)
    (hcover : (∃ x', x = d • x') ∨ (∃ y', y = d ^ (p ^ e) • y') ∨
      (j = none ∧ d ∣ root ⬝ᵥ Y h x) ∨
      (h = none ∧ d ^ (p ^ e) ∣ (fun i ↦ (Y none 1 i) ^ (p ^ e)) ⬝ᵥ Z j y)) :
    d ^ (p ^ e) ∣ (fun i ↦ (Y h x i) ^ (p ^ e)) ⬝ᵥ Z j y := by
  have scalePow (c : R) (v : n → R) :
      (fun i ↦ (c • v) i ^ (p ^ e)) = c ^ (p ^ e) • (fun i ↦ v i ^ (p ^ e)) := by
    ext i
    simp [mul_pow]
  have oneDirection (f : (Fin 1 → R) →ₗ[R] (n → R)) (v : Fin 1 → R) :
      f v = v 0 • f 1 := by
    have hv : v = v 0 • (1 : Fin 1 → R) := by
      ext i
      rw [Subsingleton.elim i 0]
      simp
    exact (congrArg f hv).trans (map_smul f ..)
  rcases hcover with ⟨x', rfl⟩ | ⟨y', rfl⟩ | ⟨rfl, hx⟩ | ⟨rfl, hy⟩
  · rw [map_smul, scalePow, smul_dotProduct, smul_eq_mul]
    exact dvd_mul_right ..
  · rw [map_smul, dotProduct_smul, smul_eq_mul]
    exact dvd_mul_right ..
  · have hy : Z none y = y (0 : Fin 1) • Z none 1 := oneDirection (Z none) y
    rw [hy, dotProduct_smul, smul_eq_mul]
    have hroot' : (fun i ↦ root i ^ (p ^ e)) = Z none 1 := funext hroot
    rw [dotProduct_comm] at hx
    exact dvd_mul_of_dvd_right (hroot' ▸ pow_dvd_dotProduct_pow hp hd hx) _
  · have hx : Y none x = x (0 : Fin 1) • Y none 1 := oneDirection (Y none) x
    rw [hx, scalePow, smul_dotProduct, smul_eq_mul]
    exact dvd_mul_of_dvd_right hy _

/-- Choosing the cheaper side for the two variable costs pays the deduction exactly. -/
private theorem pairedDirection_cost [Fintype ι] (a b : Option ι → ℕ) (q : ℕ)
    (markL markR : Bool) :
    let t := if markL then 0 else a none
    let u := if markR then 0 else b none
    let A := ∑ i, a (some i) * height i
    let B := ∑ i, b (some i) * height i
    let c := ∑ i, a (some i)
    let f := ∑ i, b (some i)
    let leftOne := t ≤ q * (f + u)
    let leftTall := A ≤ q * B
    let l (h : Option ι) := h.elim (if !markL && decide leftOne then 1 else 0)
      (fun i ↦ (if leftTall then height i else 0) + 1)
    let r (h : Option ι) :=
      (if h.isSome && !decide leftTall then directionBlockSize height h else 0) +
      (if !markL && !decide leftOne && (h.isSome || !markR) then 1 else 0)
    (∑ h, a h * l h) + q * (∑ h, b h * r h) =
      min t (q * (f + u)) + c + min A (q * B) := by
  classical
  dsimp only
  rw [Fintype.sum_option, Fintype.sum_option]
  split_ifs <;> simp_all only [Finset.sum_add_distrib, Nat.mul_add, min_def,
    zero_add, add_zero, mul_zero, mul_one, Option.elim_none, Option.elim_some,
    Option.isSome_none, Option.isSome_some, Bool.true_and, Bool.false_and, Bool.true_or,
    Bool.false_or, Bool.and_true, Bool.and_false, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.not_eq_eq_eq_not, decide_eq_true_eq,
    not_le, zero_le, ite_true, ite_false, mul_ite, sum_ite_irrel, sum_const_zero] <;>
    (try split_ifs) <;>
    simp_all (config := { failIfUnchanged := false }) only
      [not_true_eq_false, decide_true, decide_false, Bool.true_eq_false] <;> omega

/-- Every nonexempt pair is covered by either a block scaling or a linear test. -/
private theorem directionChoices_cover (markL markR leftOne leftTall : Bool) (h j : Option ι)
    (he : ¬(h = none ∧ (markL = true ∨ j = none ∧ markR = true))) :
    h.elim (!markL && leftOne) (fun _ ↦ leftTall) = true ∨
    (j.isSome && !leftTall) = true ∨ (j = none ∧ h.isSome = true) ∨
    (h = none ∧ (!markL && !leftOne && (j.isSome || !markR)) = true) := by
  cases h with
  | none =>
    have hmarkL : markL = false := by cases markL <;> simp_all
    cases leftOne with
    | true => exact .inl (by simp [hmarkL])
    | false =>
      refine .inr (.inr (.inr ⟨rfl, ?_⟩))
      cases j <;> cases markR <;> simp_all
  | some i =>
    cases j with
    | none => exact .inr (.inr (.inl ⟨rfl, rfl⟩))
    | some j => cases leftTall <;> simp

/-- For two families of theta directions at a place and its partner, impose coefficient
submodules that make all nonexempt pairings divisible by `d^(p^e)`. The `none` blocks have
height one, and `some i` has height `height i`. A pair is exempt only when its left block is
`none` and either its left place is marked or its right block is `none` at a marked place.

The weighted sum of the colength exponents, measured in powers of `d`, is the sum of the
two minimum costs and the number of taller columns on the left. The exponent on the right
is measured first in powers of `d^(p^e)`, so its contribution is multiplied by `p^e`.
The submodules can be intersected before extracting any determinant witnesses. -/
theorem exists_colengthDvd_frobenius_pairing [PreValuationRing R] [Fintype ι]
    {p e : ℕ} (hp : p.Prime) {d : R} (hd : d ^ (p ^ e) ∣ (p : R))
    (Y Z : ∀ h : Option ι, (Fin (h.elim 1 height) → R) →ₗ[R] (n → R))
    (root : n → R) (hroot : ∀ i, root i ^ (p ^ e) = Z none 1 i)
    (a b : Option ι → ℕ) (markL markR : Bool) :
    ∃ (L M : ∀ h : Option ι, Submodule R (Fin (h.elim 1 height) → R)) (l r : Option ι → ℕ),
      (∀ h, (⊤ : Submodule R _).ColengthDvd (L h) (d ^ l h)) ∧
      (∀ h, (⊤ : Submodule R _).ColengthDvd (M h) ((d ^ (p ^ e)) ^ r h)) ∧
      ((∑ h, a h * l h) + p ^ e * (∑ h, b h * r h) =
        min (if markL then 0 else a none)
          (p ^ e * ((∑ i, b (some i)) + if markR then 0 else b none)) +
        (∑ i, a (some i)) +
        min (∑ i, a (some i) * height i) (p ^ e * (∑ i, b (some i) * height i))) ∧
      (∀ h j, ¬(h = none ∧ (markL = true ∨ j = none ∧ markR = true)) →
        ∀ x ∈ L h, ∀ y ∈ M j,
        d ^ (p ^ e) ∣ (fun i ↦ (Y h x i) ^ (p ^ e)) ⬝ᵥ Z j y) := by
  classical
  let q := p ^ e
  let leftOne := (if markL then 0 else a none) ≤
    q * ((∑ i, b (some i)) + if markR then 0 else b none)
  let leftTall := (∑ i, a (some i) * height i) ≤ q * (∑ i, b (some i) * height i)
  let sL (h : Option ι) := h.elim (!markL && decide leftOne) (fun _ ↦ decide leftTall)
  let sR (h : Option ι) := h.isSome && !decide leftTall
  let tR (h : Option ι) := !markL && !decide leftOne && (h.isSome || !markR)
  let fL (h : Option ι) := (dotProductBilin R R root).comp (Y h)
  let fR (h : Option ι) := (dotProductBilin R R (fun i ↦ Y none 1 i ^ q)).comp (Z h)
  let L (h : Option ι) : Submodule R _ :=
    (if sL h then d • ⊤ else ⊤) ⊓ (if h.isSome then Submodule.comap (fL h) (Ideal.span {d}) else ⊤)
  let M (h : Option ι) : Submodule R _ :=
    (if sR h then d ^ q • ⊤ else ⊤) ⊓
      (if tR h then Submodule.comap (fR h) (Ideal.span {d ^ q}) else ⊤)
  let l (h : Option ι) := (if sL h then directionBlockSize height h else 0) +
    (if h.isSome then 1 else 0)
  let r (h : Option ι) := (if sR h then directionBlockSize height h else 0) +
    (if tR h then 1 else 0)
  refine ⟨L, M, l, r, fun h ↦ directionConstraints _ d (fL h) (sL h = true) (h.isSome = true),
    fun h ↦ directionConstraints _ (d ^ q) (fR h) (sR h = true) (tR h = true), ?_, ?_⟩
  · have hl (h : Option ι) : l h = h.elim (if !markL && decide leftOne then 1 else 0)
        (fun i ↦ (if leftTall then height i else 0) + 1) := by
      cases h <;> simp [l, sL, directionBlockSize]
    simpa only [hl] using pairedDirection_cost (height := height) a b q markL markR
  · intro h j he x hx y hy
    apply dvd_of_direction_cover hp hd Y Z root hroot x y
    have hsL (hs : sL h = true) : ∃ x', x = d • x' := by
      simpa [eq_comm] using (Submodule.mem_smul_pointwise_iff_exists x d ⊤).mp
        (by simpa only [hs, ite_true] using (Submodule.mem_inf.mp hx).1)
    have hsR (hs : sR j = true) : ∃ y', y = d ^ q • y' := by
      simpa [eq_comm] using (Submodule.mem_smul_pointwise_iff_exists y (d ^ q) ⊤).mp
        (by simpa only [hs, ite_true] using (Submodule.mem_inf.mp hy).1)
    have htL (ht : h.isSome = true) : d ∣ root ⬝ᵥ Y h x := by
      have hmem : fL h x ∈ Ideal.span {d} := by
        simpa only [ht, ite_true, Submodule.mem_comap] using (Submodule.mem_inf.mp hx).2
      simpa only [fL, LinearMap.comp_apply, dotProductBilin_apply_apply] using
        Ideal.mem_span_singleton.mp hmem
    have htR (ht : tR j = true) : d ^ q ∣ (fun i ↦ Y none 1 i ^ q) ⬝ᵥ Z j y := by
      have hmem : fR j y ∈ Ideal.span {d ^ q} := by
        simpa only [ht, ite_true, Submodule.mem_comap] using (Submodule.mem_inf.mp hy).2
      simpa only [fR, LinearMap.comp_apply, dotProductBilin_apply_apply] using
        Ideal.mem_span_singleton.mp hmem
    rcases directionChoices_cover markL markR (decide leftOne) (decide leftTall) h j he with
      hs | hs | ⟨hj, ht⟩ | ⟨hh, ht⟩
    · exact .inl (hsL hs)
    · exact .inr (.inl (hsR hs))
    · exact .inr (.inr (.inl ⟨hj, htL ht⟩))
    · exact .inr (.inr (.inr ⟨hh, htR ht⟩))

end PairedDirections

end TauCeti
