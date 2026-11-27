/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Algebra.BigOperators.Pi

/-!
# Walsh characters and the Walsh expansion on the Boolean cube

The *Boolean cube* is the additive group `ι → ZMod 2` of `ι`-indexed bit vectors. For a finite
set `S` of coordinates, the *Walsh character* `walsh S` sends `x` to `∏ i ∈ S, (-1) ^ x i`; under
the dictionary sending a bit `a` to the sign `(-1) ^ a`, it is the monomial `∏ i ∈ S, x i` on the
cube `{±1}^ι`. This file develops the expansion of real functions on the cube in these
characters, the starting point of the Fourier analysis of Boolean functions.

## Main definitions

* `TauCeti.walsh S`: the Walsh character of a finite set `S` of coordinates.
* `TauCeti.walshAddChar S`: `walsh S` bundled as an additive character of the cube.
* `TauCeti.walshCoeff f S`: the Fourier–Walsh coefficient `𝔼 x, f x * walsh S x` of a real
  function `f` on a finite cube.

## Main results

* `TauCeti.walsh_add`, `TauCeti.walsh_zero`: `walsh S` is an additive character.
* `TauCeti.walsh_mul_walsh`: `walsh S * walsh T = walsh (S ∆ T)`.
* `TauCeti.existsUnique_walsh_eq_addChar`: on a finite cube every real additive character is
  `walsh S` for exactly one `S`.
* `TauCeti.expect_walsh`, `TauCeti.expect_walsh_mul_walsh`: the average of `walsh S` is `1` or
  `0` according as `S` is empty or not, and the Walsh characters are orthonormal.
* `TauCeti.sum_walshCoeff_mul_walsh`: the Walsh expansion
  `∑ S, walshCoeff f S * walsh S x = f x`, with the uniqueness of its coefficients
  `TauCeti.walshCoeff_sum_mul_walsh` and `TauCeti.walshCoeff_injective`.

## References

* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014
  (arXiv:2105.10386), Chapter 1: Definition 1.2, Facts 1.6, 1.7 and 1.12, Theorems 1.1 and 1.5,
  Proposition 1.8.
* R. de Wolf, *A Brief Introduction to Fourier Analysis on the Boolean Cube*, Theory of
  Computing Library, Graduate Surveys 1 (2008), Section 2.
-/

public section

open Finset
open scoped BigOperators

namespace TauCeti

variable {ι : Type*}

/-! ### Walsh characters -/

/-- The **Walsh character** of a finite set `S` of coordinates: the real function on the cube
`ι → ZMod 2` sending `x` to `∏ i ∈ S, (-1) ^ x i`. Its values are `±1`. -/
noncomputable def walsh (S : Finset ι) (x : ι → ZMod 2) : ℝ :=
  ∏ i ∈ S, (-1 : ℝ) ^ (x i).val

lemma walsh_def (S : Finset ι) (x : ι → ZMod 2) :
    walsh S x = ∏ i ∈ S, (-1 : ℝ) ^ (x i).val := (rfl)

@[simp] lemma walsh_empty : walsh (∅ : Finset ι) = 1 := by
  ext x
  simp [walsh_def]

lemma walsh_singleton (i : ι) (x : ι → ZMod 2) : walsh {i} x = (-1) ^ (x i).val := by
  simp [walsh_def]

lemma walsh_insert [DecidableEq ι] {i : ι} {S : Finset ι} (hi : i ∉ S) (x : ι → ZMod 2) :
    walsh (insert i S) x = (-1) ^ (x i).val * walsh S x :=
  prod_insert hi

@[simp] lemma walsh_zero (S : Finset ι) : walsh S 0 = 1 := by
  simp [walsh_def]

lemma walsh_add (S : Finset ι) (x y : ι → ZMod 2) :
    walsh S (x + y) = walsh S x * walsh S y := by
  simp only [walsh_def, Pi.add_apply, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [← pow_add, ZMod.val_add, ← neg_one_pow_eq_pow_mod_two]

@[simp] lemma walsh_mul_self (S : Finset ι) (x : ι → ZMod 2) : walsh S x * walsh S x = 1 := by
  simp [walsh_def, ← prod_mul_distrib, ← mul_pow]

@[simp] lemma walsh_sq (S : Finset ι) (x : ι → ZMod 2) : walsh S x ^ 2 = 1 := by
  rw [sq, walsh_mul_self]

/-- The Walsh characters are sign-valued. -/
lemma walsh_eq_one_or_eq_neg_one (S : Finset ι) (x : ι → ZMod 2) :
    walsh S x = 1 ∨ walsh S x = -1 :=
  mul_self_eq_one_iff.1 (walsh_mul_self S x)

@[simp] lemma abs_walsh (S : Finset ι) (x : ι → ZMod 2) : |walsh S x| = 1 := by
  rcases walsh_eq_one_or_eq_neg_one S x with h | h <;> simp [h]

lemma walsh_ne_zero (S : Finset ι) (x : ι → ZMod 2) : walsh S x ≠ 0 := by
  rcases walsh_eq_one_or_eq_neg_one S x with h | h <;> simp [h]

/-- The product of two Walsh characters is the Walsh character of the symmetric difference. -/
lemma walsh_mul_walsh [DecidableEq ι] (S T : Finset ι) (x : ι → ZMod 2) :
    walsh S x * walsh T x = walsh (symmDiff S T) x := by
  have hS := prod_inter_mul_prod_sdiff S T fun i ↦ (-1 : ℝ) ^ (x i).val
  have hT := prod_inter_mul_prod_sdiff T S fun i ↦ (-1 : ℝ) ^ (x i).val
  rw [inter_comm] at hT
  have hST : walsh (S ∩ T) x * walsh (S ∩ T) x = 1 := walsh_mul_self _ x
  rw [walsh_def, walsh_def, ← hS, ← hT, Finset.symmDiff_def, walsh_def,
    prod_union disjoint_sdiff_sdiff]
  simp only [walsh_def] at hST
  linear_combination (∏ i ∈ S \ T, (-1 : ℝ) ^ (x i).val) *
    (∏ i ∈ T \ S, (-1 : ℝ) ^ (x i).val) * hST

/-- The value of a Walsh character at the point with a single nonzero entry, at `i`: it is `-1`
if `i ∈ S` and `1` otherwise. -/
lemma walsh_single_one [DecidableEq ι] (S : Finset ι) (i : ι) :
    walsh S (Pi.single i 1) = if i ∈ S then -1 else 1 := by
  rw [walsh_def, ← prod_ite_eq' S i fun _ ↦ (-1 : ℝ)]
  refine prod_congr rfl fun j _ ↦ ?_
  rcases eq_or_ne j i with rfl | hj
  · simp [ZMod.val_one]
  · simp [hj]

/-- Distinct finite sets of coordinates have distinct Walsh characters. -/
lemma walsh_injective : Function.Injective (walsh : Finset ι → (ι → ZMod 2) → ℝ) := by
  classical
  intro S T h
  ext i
  have hi := congrFun h (Pi.single i 1)
  rw [walsh_single_one, walsh_single_one] at hi
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp only [hS, hT, ite_true, ite_false] at hi ⊢
  all_goals norm_num at hi

@[simp] lemma walsh_inj {S T : Finset ι} : walsh S = walsh T ↔ S = T :=
  walsh_injective.eq_iff

/-- The Walsh character `walsh S` as an additive character of the cube `ι → ZMod 2`. -/
noncomputable def walshAddChar (S : Finset ι) : AddChar (ι → ZMod 2) ℝ where
  toFun := walsh S
  map_zero_eq_one' := walsh_zero S
  map_add_eq_mul' := walsh_add S

@[simp] lemma coe_walshAddChar (S : Finset ι) : ⇑(walshAddChar S) = walsh S := (rfl)

@[simp] lemma walshAddChar_eq_zero_iff {S : Finset ι} : walshAddChar S = 0 ↔ S = ∅ := by
  rw [← AddChar.coe_eq_one, coe_walshAddChar, ← walsh_empty, walsh_inj]

/-- **Classification of the real characters of the cube.** On a finite cube, every additive
character with real values is the Walsh character of exactly one set of coordinates. -/
theorem existsUnique_walsh_eq_addChar [Finite ι] (ψ : AddChar (ι → ZMod 2) ℝ) :
    ∃! S : Finset ι, ⇑ψ = walsh S := by
  classical
  have := Fintype.ofFinite ι
  -- A real character of the cube takes the values `±1` on the points `Pi.single i 1`.
  have hsign (i : ι) : ψ (Pi.single i 1) = 1 ∨ ψ (Pi.single i 1) = -1 := by
    refine mul_self_eq_one_iff.1 ?_
    rw [← AddChar.map_add_eq_mul, ← Pi.single_add, show (1 + 1 : ZMod 2) = 0 from rfl,
      Pi.single_zero, AddChar.map_zero_eq_one]
  set S : Finset ι := {i | ψ (Pi.single i 1) = -1}
  -- Both `ψ` and `walsh S` are additive monoid homomorphisms into `Additive ℝ` that agree on
  -- the points with a single nonzero entry, so they agree everywhere.
  have hS : ⇑ψ = walsh S := by
    rw [← coe_walshAddChar, DFunLike.coe_fn_eq, ← AddChar.toAddMonoidHomEquiv.apply_eq_iff_eq]
    refine AddMonoidHom.functions_ext _ _ _ fun i a ↦ ?_
    simp only [AddChar.toAddMonoidHomEquiv_apply, coe_walshAddChar, EmbeddingLike.apply_eq_iff_eq]
    obtain rfl | rfl : a = 0 ∨ a = 1 := by decide +revert
    · simp
    · rw [walsh_single_one]
      rcases hsign i with h | h <;> simp [S, h]
  exact ⟨S, hS, fun T hT ↦ walsh_injective (hT.symm.trans hS)⟩

/-! ### Averages of Walsh characters -/

section Fintype

variable [Fintype ι] [DecidableEq ι]

/-- The average of a Walsh character over the cube is `1` for the empty set and `0` otherwise. -/
lemma expect_walsh (S : Finset ι) : 𝔼 x, walsh S x = if S = ∅ then 1 else 0 := by
  simp_rw [← coe_walshAddChar, AddChar.expect_eq_ite, walshAddChar_eq_zero_iff]

/-- **Orthonormality of the Walsh characters.** -/
lemma expect_walsh_mul_walsh (S T : Finset ι) :
    𝔼 x, walsh S x * walsh T x = if S = T then 1 else 0 := by
  simp_rw [walsh_mul_walsh, expect_walsh, symmDiff_eq_empty]

omit [DecidableEq ι] in
/-- The sum of all Walsh characters at `x` is `2 ^ n` at `x = 0` and vanishes elsewhere, where
`n` is the number of coordinates. -/
lemma sum_walsh (x : ι → ZMod 2) :
    ∑ S, walsh S x = if x = 0 then 2 ^ Fintype.card ι else 0 := by
  have h : ∑ S, walsh S x = ∏ i, (1 + (-1 : ℝ) ^ (x i).val) := by
    rw [prod_one_add, powerset_univ]
    simp only [walsh_def]
  rw [h]
  split_ifs with hx
  · subst hx
    norm_num
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra! h
      exact hx (funext h)
    refine prod_eq_zero (mem_univ i) ?_
    generalize x i = a at hi
    obtain rfl : a = 1 := by decide +revert
    norm_num [show (1 : ZMod 2).val = 1 from rfl]

/-! ### Walsh coefficients -/

/-- The **Walsh coefficient** of a real function `f` on the cube at a set `S` of coordinates:
the average of `f` against the Walsh character `walsh S`. -/
noncomputable def walshCoeff (f : (ι → ZMod 2) → ℝ) (S : Finset ι) : ℝ :=
  𝔼 x, f x * walsh S x

lemma walshCoeff_def (f : (ι → ZMod 2) → ℝ) (S : Finset ι) :
    walshCoeff f S = 𝔼 x, f x * walsh S x := (rfl)

/-- The coefficient at the empty set is the mean of the function. -/
@[simp] lemma walshCoeff_empty (f : (ι → ZMod 2) → ℝ) : walshCoeff f ∅ = 𝔼 x, f x := by
  simp [walshCoeff_def]

@[simp] lemma walshCoeff_zero (S : Finset ι) : walshCoeff 0 S = 0 := by
  simp [walshCoeff_def]

@[simp] lemma walshCoeff_add (f g : (ι → ZMod 2) → ℝ) (S : Finset ι) :
    walshCoeff (f + g) S = walshCoeff f S + walshCoeff g S := by
  simp [walshCoeff_def, add_mul, expect_add_distrib]

@[simp] lemma walshCoeff_smul (c : ℝ) (f : (ι → ZMod 2) → ℝ) (S : Finset ι) :
    walshCoeff (c • f) S = c * walshCoeff f S := by
  simp [walshCoeff_def, mul_assoc, mul_expect]

@[simp] lemma walshCoeff_neg (f : (ι → ZMod 2) → ℝ) (S : Finset ι) :
    walshCoeff (-f) S = -walshCoeff f S := by
  simpa using walshCoeff_smul (-1) f S

@[simp] lemma walshCoeff_sub (f g : (ι → ZMod 2) → ℝ) (S : Finset ι) :
    walshCoeff (f - g) S = walshCoeff f S - walshCoeff g S := by
  simp [sub_eq_add_neg]

lemma walshCoeff_sum {κ : Type*} (s : Finset κ) (f : κ → (ι → ZMod 2) → ℝ) (S : Finset ι) :
    walshCoeff (∑ k ∈ s, f k) S = ∑ k ∈ s, walshCoeff (f k) S := by
  simp_rw [walshCoeff_def, Finset.sum_apply, sum_mul]
  exact expect_sum_comm _ _ _

/-- The Walsh coefficients of a constant function vanish away from the empty set. -/
@[simp] lemma walshCoeff_const (c : ℝ) (S : Finset ι) :
    walshCoeff (fun _ ↦ c) S = if S = ∅ then c else 0 := by
  simp [walshCoeff_def, ← mul_expect, expect_walsh]

/-- The Walsh coefficients of a Walsh character. -/
@[simp] lemma walshCoeff_walsh (S T : Finset ι) :
    walshCoeff (walsh T) S = if S = T then 1 else 0 := by
  simp only [walshCoeff_def, expect_walsh_mul_walsh, @eq_comm _ T]

/-- **Uniqueness of the Walsh expansion.** A combination of Walsh characters has its
coefficients as Walsh coefficients. -/
lemma walshCoeff_sum_mul_walsh (c : Finset ι → ℝ) (S : Finset ι) :
    walshCoeff (fun x ↦ ∑ T, c T * walsh T x) S = c S := by
  simp_rw [walshCoeff_def, sum_mul, mul_assoc]
  rw [expect_sum_comm]
  simp_rw [← mul_expect, expect_walsh_mul_walsh, mul_ite, mul_one, mul_zero]
  simp [eq_comm]

/-- If `f` is a combination of Walsh characters, its coefficients are the Walsh coefficients of
`f`. -/
lemma eq_walshCoeff_of_forall_eq_sum {f : (ι → ZMod 2) → ℝ} {c : Finset ι → ℝ}
    (h : ∀ x, f x = ∑ S, c S * walsh S x) (S : Finset ι) : c S = walshCoeff f S := by
  rw [funext h, walshCoeff_sum_mul_walsh]

/-- **The Walsh expansion.** Every real function on the cube is the combination of the Walsh
characters with its Walsh coefficients. -/
theorem sum_walshCoeff_mul_walsh (f : (ι → ZMod 2) → ℝ) (x : ι → ZMod 2) :
    ∑ S, walshCoeff f S * walsh S x = f x := by
  calc ∑ S, walshCoeff f S * walsh S x = 𝔼 y, f y * ∑ S, walsh S (y + x) := by
        simp_rw [walshCoeff_def, expect_mul, mul_sum, walsh_add, mul_assoc]
        exact (expect_sum_comm _ _ _).symm
    _ = f x := by
        have hyx (y : ι → ZMod 2) : y + x = 0 ↔ y = x := by
          rw [add_eq_zero_iff_eq_neg]
          refine Eq.congr_right (funext fun i ↦ ?_)
          exact ZMod.neg_eq_self_mod_two (x i)
        simp_rw [sum_walsh, hyx, mul_ite, mul_zero, Fintype.expect_eq_sum_div_card,
          sum_ite_eq', mem_univ, ite_true, Fintype.card_fun, ZMod.card, Nat.cast_pow,
          Nat.cast_ofNat]
        field_simp

/-- A real function on the cube is determined by its Walsh coefficients. -/
lemma walshCoeff_injective :
    Function.Injective (walshCoeff : ((ι → ZMod 2) → ℝ) → Finset ι → ℝ) := by
  intro f g h
  ext x
  rw [← sum_walshCoeff_mul_walsh f, ← sum_walshCoeff_mul_walsh g, h]

@[simp] lemma walshCoeff_inj {f g : (ι → ZMod 2) → ℝ} : walshCoeff f = walshCoeff g ↔ f = g :=
  walshCoeff_injective.eq_iff

end Fintype

end TauCeti
