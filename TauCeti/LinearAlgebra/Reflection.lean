/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Reflection
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import TauCeti.RingTheory.Polynomial.Chebyshev.Growth
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Module reflections

This file computes the determinant of Mathlib's `Module.reflection` on a finite free module, and
records that a reflection negates the linear form defining it. Consequently a finite free module
of positive rank has a linear automorphism of determinant `-1`.

It also computes the fixed vectors of a product of reflections `y ↦ y - fᵢ(y) • vᵢ` along
linearly independent vectors `vᵢ`, each used at most once: they are exactly the common zeros of the
linear forms `fᵢ` (`Module.list_prod_map_preReflection_apply_eq_self_iff`). Applied to the simple
roots of a base of a root pairing, this computes the fixed vectors of a Coxeter element.

Finally it computes the order of the product `r₁ r₂` of two reflections `r₁ z = z - f(z) x` and
`r₂ z = z - g(z) y` from their Cartan product `c = f(y) g(x)`, with no root system or inner
product around. If `f(y) = g(x) = 0`, or `c = 1, 2, 3`, then `(r₁ r₂)ᵐ = 1` for `m = 2, 3, 4, 6`;
when `x` and `y` are linearly independent, `2 ≠ 0` and, for `c = 3`, `g(x) ≠ 0`, these are the
exact orders, and over a
ring of characteristic zero an integral Cartan product `c ≥ 4` gives infinite order. This is
the rank-two computation behind the Weyl group of a Kac–Moody realization, where the simple roots
need not belong to any finite root system.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  § 3.16, for the argument by linear independence in the case of the simple roots.
* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Proposition 3.13, for the orders
  of products of two simple reflections read off the Cartan product.

The iterates of `r₁ r₂` are Mathlib's `Module.reflection_mul_reflection_pow_apply` and
`Module.reflection_mul_reflection_pow_apply_self`, in terms of the Chebyshev polynomials
`Polynomial.Chebyshev.S`. The evaluation of their coefficients at `c - 2 = -1, 0, 1` follows the
root-pairing case in `TauCeti.LinearAlgebra.RootSystem.BraidRelation`.
-/

public section

universe u v

namespace Module

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {x : M} {f : Module.Dual R M} (h : f x = 2)

/-- The determinant of a module reflection is `-1` on a finite free module. -/
@[simp]
theorem det_reflection [Module.Free R M] [Module.Finite R M] :
    LinearEquiv.det (reflection h) = (-1 : Rˣ) := by
  apply Units.ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix (Module.Free.chooseBasis R M)]
  let b := Module.Free.chooseBasis R M
  rw [reflection]
  -- Unfold the reflection into its rank-one perturbation before applying the determinant lemma.
  change Matrix.det (LinearMap.toMatrix b b (LinearMap.id - f.smulRight x)) = -1
  rw [map_sub, LinearMap.toMatrix_id, LinearMap.toMatrix_smulRight]
  -- The rank-one determinant lemma is stated for a column matrix times a row matrix.
  rw [show Matrix.vecMulVec (b.repr x) (f ∘ b) =
      Matrix.replicateCol Unit (b.repr x) * Matrix.replicateRow Unit (f ∘ b) by
      ext i j
      simp [Matrix.mul_apply, Matrix.vecMulVec_apply]]
  rw [sub_eq_add_neg, ← Matrix.neg_mul]
  -- Put the matrix in the exact Schur-complement rank-one form.
  change Matrix.det
    (1 + Matrix.replicateCol Unit (-b.repr x) * Matrix.replicateRow Unit (f ∘ b)) = -1
  rw [Matrix.det_one_add_replicateCol_mul_replicateRow]
  -- The remaining scalar is `1 - f x = -1`.
  change 1 + ∑ i, f (b i) * -(b.repr x i) = -1
  simp_rw [mul_neg, mul_comm (f (b _))]
  rw [Finset.sum_neg_distrib]
  have hsum : ∑ i, b.repr x i * f (b i) = f x := by
    calc
      _ = ∑ i, f ((b.repr x i) • b i) := by
        simp only [map_smul, smul_eq_mul]
      _ = f (∑ i, (b.repr x i) • b i) := by rw [map_sum]
      _ = f x := congrArg f (b.sum_repr x)
  rw [hsum, h]
  ring

include h in
/-- The reflection `Module.preReflection x f` negates the linear form `f` defining it. -/
@[simp]
theorem apply_preReflection (y : M) : f (preReflection x f y) = -f y := by
  rw [preReflection_apply, map_sub, map_smul, smul_eq_mul, h]
  ring

/-- A finite free module of positive rank has a linear automorphism of determinant `-1`, namely
a reflection in a basis vector. -/
theorem exists_det_eq_neg_one [Module.Free R M] [Module.Finite R M]
    (hM : 0 < finrank R M) : ∃ g : M ≃ₗ[R] M, LinearEquiv.det g = -1 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨LinearEquiv.refl R M, Subsingleton.elim _ _⟩
  let b := Module.Free.chooseBasis R M
  have := Module.nontrivial_of_finrank_pos (R := R) hM
  obtain ⟨i⟩ := b.index_nonempty
  have hf : (2 • b.coord i) (b i) = 2 := by simp
  exact ⟨reflection hf, det_reflection hf⟩

section ListProd

variable {ι : Type*} {v : ι → M} {g : ι → Dual R M}

/-- A product of reflections along the vectors `v i`, `i ∈ l`, moves every vector by an element of
the span of those vectors. -/
theorem list_prod_map_preReflection_apply_sub_mem_span (l : List ι) (y : M) :
    (l.map fun i ↦ preReflection (v i) (g i)).prod y - y ∈
      Submodule.span R (v '' {i | i ∈ l}) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, mul_apply_eq_comp, preReflection_apply, sub_right_comm]
    refine sub_mem (Submodule.span_mono (Set.image_mono fun j hj ↦ ?_) ih)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simp, rfl⟩))
    exact List.mem_cons_of_mem i hj

/-- **Fixed vectors of a product of reflections in linearly independent vectors.** Let `l` list
distinct indices, and let the vectors `v i` be linearly independent. The product of the
reflections `y ↦ y - g i y • v i` over `i ∈ l`, in the order of `l`, fixes `y` exactly when every
linear form `g i` with `i ∈ l` vanishes on `y`. Thus its fixed space is the intersection of the
kernels of the `g i`. -/
theorem list_prod_map_preReflection_apply_eq_self_iff (hv : LinearIndependent R v) {l : List ι}
    (hl : l.Nodup) {y : M} :
    (l.map fun i ↦ preReflection (v i) (g i)).prod y = y ↔ ∀ i ∈ l, g i y = 0 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, mul_apply_eq_comp, preReflection_apply, List.forall_mem_cons,
      ← ih hl.2]
    set z := (l.map fun i ↦ preReflection (v i) (g i)).prod y
    -- The vectors `g i z • v i` and `z - y` lie in the spans of disjoint sets of the `v j`.
    have hdisj := hv.disjoint_span_image (s := {i}) (t := {j | j ∈ l})
      (Set.disjoint_singleton_left.mpr hl.1)
    refine ⟨fun h ↦ ?_, fun ⟨hi, hz⟩ ↦ by rw [hz, hi, zero_smul, sub_zero]⟩
    have hzero : g i z • v i = 0 := by
      refine Submodule.disjoint_def.mp hdisj _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl, rfl⟩)) ?_
      rw [show g i z • v i = z - y by rw [← h, sub_sub_cancel]]
      exact list_prod_map_preReflection_apply_sub_mem_span l y
    have hgz : g i z = 0 := hv.smul_left_injective i (by simp only [hzero, zero_smul])
    rw [hgz, zero_smul, sub_zero] at h
    exact ⟨h ▸ hgz, h⟩

end ListProd

section Pair

open Polynomial.Chebyshev

variable {x y : M} {f g : Dual R M} (hf : f x = 2) (hg : g y = 2)

/-- **Two reflections each fixing the other's vector commute**, and their product is an
involution: if `f y = 0` and `g x = 0`, then `(r₁ r₂)² = 1`. -/
theorem reflection_mul_reflection_pow_two_eq_one (hfy : f y = 0) (hgx : g x = 0) :
    (reflection hf * reflection hg) ^ 2 = 1 := by
  ext z
  -- At `t = -2` the two coefficients of the general formula are `1` and `-1`, and the two
  -- displacement terms cancel because `f y = g x = 0`.
  rw [reflection_mul_reflection_pow_apply hf hg 2 z (-2) (by rw [hfy]; ring)]
  norm_num [hfy, hgx, S_zero, S_one, S_neg_one]
  abel

/-- **The braid relation at Cartan product `1`**: if `f y * g x = 1`, then `(r₁ r₂)³ = 1`, the
`A₂` configuration. -/
theorem reflection_mul_reflection_pow_three_eq_one (h : f y * g x = 1) :
    (reflection hf * reflection hg) ^ 3 = 1 := by
  ext z
  -- At `t = -1` both coefficients of the general formula carry the factor `S₁(t) + S₀(t) = 0`.
  rw [reflection_mul_reflection_pow_apply hf hg 3 z (-1) (by rw [h]; ring)]
  norm_num [S_zero, S_one]

/-- **The braid relation at Cartan product `2`**: if `f y * g x = 2`, then `(r₁ r₂)⁴ = 1`, the
`B₂` configuration. -/
theorem reflection_mul_reflection_pow_four_eq_one (h : f y * g x = 2) :
    (reflection hf * reflection hg) ^ 4 = 1 := by
  ext z
  -- At `t = 0` both coefficients of the general formula carry the factor `S₁(t) = t = 0`.
  rw [reflection_mul_reflection_pow_apply hf hg 4 z 0 (by rw [h]; ring)]
  norm_num [S_zero, S_one]

/-- **The braid relation at Cartan product `3`**: if `f y * g x = 3`, then `(r₁ r₂)⁶ = 1`, the
`G₂` configuration. -/
theorem reflection_mul_reflection_pow_six_eq_one (h : f y * g x = 3) :
    (reflection hf * reflection hg) ^ 6 = 1 := by
  ext z
  -- At `t = 1` both coefficients of the general formula carry the factor `S₂(t) = t² - 1 = 0`.
  rw [reflection_mul_reflection_pow_apply hf hg 6 z 1 (by rw [h]; ring)]
  norm_num [S_two]

variable {hf hg}

/-- If a power `(r₁ r₂)ⁿ` of the product of the reflections in two linearly independent vectors
is trivial, the two coefficients of `(r₁ r₂)ⁿ x` are those of `x`. -/
private theorem eval_S_eq_of_pow_eq_one (hxy : LinearIndependent R ![x, y]) {n : ℕ}
    (hn : (reflection hf * reflection hg) ^ n = 1) :
    (S R n).eval (f y * g x - 2) + (S R (n - 1)).eval (f y * g x - 2) = 1 ∧
      (S R (n - 1)).eval (f y * g x - 2) * g x = 0 := by
  have h := reflection_mul_reflection_pow_apply_self hf hg n
  rw [hn, FunLike.coe_one_eq_id, id_eq] at h
  have h' : (1 : R) • x + (0 : R) • y =
      ((S R n).eval (f y * g x - 2) + (S R (n - 1)).eval (f y * g x - 2)) • x +
        ((S R (n - 1)).eval (f y * g x - 2) * -g x) • y := by
    rw [one_smul, zero_smul, add_zero]
    exact h
  obtain ⟨h₁, h₂⟩ := hxy.eq_of_pair h'
  exact ⟨h₁.symm, by linear_combination h₂⟩

/-- **The product of two reflections each fixing the other's vector has order `2`**: if the
vectors are linearly independent, `f y = 0`, `g x = 0` and `2 ≠ 0`, then `r₁ r₂` has order
exactly `2`. -/
theorem orderOf_reflection_mul_reflection_eq_two [NeZero (2 : R)]
    (hxy : LinearIndependent R ![x, y]) (hfy : f y = 0) (hgx : g x = 0) :
    orderOf (reflection hf * reflection hg) = 2 := by
  refine orderOf_eq_prime (reflection_mul_reflection_pow_two_eq_one hf hg hfy hgx) fun h1 ↦ ?_
  have := (eval_S_eq_of_pow_eq_one hxy (n := 1) (by rw [pow_one, h1])).1
  norm_num [hfy, S_zero, S_one] at this
  exact (two_ne_zero : (2 : R) ≠ 0) (by linear_combination -this)

/-- **At Cartan product `1` the product of the reflections in two linearly independent vectors
has order exactly `3`**, over any nontrivial ring. -/
theorem orderOf_reflection_mul_reflection_eq_three [Nontrivial R]
    (hxy : LinearIndependent R ![x, y]) (h : f y * g x = 1) :
    orderOf (reflection hf * reflection hg) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (reflection_mul_reflection_pow_three_eq_one hf hg h) fun h1 ↦ ?_
  have := (eval_S_eq_of_pow_eq_one hxy (n := 1) (by rw [pow_one, h1])).1
  norm_num [h, S_zero, S_one] at this

/-- **At Cartan product `2` the product of the reflections in two linearly independent vectors
has order exactly `4`**, provided `2 ≠ 0`. -/
theorem orderOf_reflection_mul_reflection_eq_four [NeZero (2 : R)]
    (hxy : LinearIndependent R ![x, y]) (h : f y * g x = 2) :
    orderOf (reflection hf * reflection hg) = 4 := by
  refine orderOf_eq_of_pow_and_pow_div_prime
    (reflection_mul_reflection_pow_four_eq_one hf hg h) fun p hp hpd ↦ ?_
  obtain rfl : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow (n := 2) hpd)
  intro h2
  have := (eval_S_eq_of_pow_eq_one hxy (n := 2) h2).1
  norm_num [h, S_one, S_two] at this
  exact (two_ne_zero : (2 : R) ≠ 0) (by linear_combination -this)

/-- **At Cartan product `3` the product of the reflections in two linearly independent vectors
has order exactly `6`**, provided `2 ≠ 0` and `g x ≠ 0`. The latter holds automatically when `R`
has no zero divisors, since `f y * g x = 3` and `3 ≠ 0` then. -/
theorem orderOf_reflection_mul_reflection_eq_six [NeZero (2 : R)]
    (hxy : LinearIndependent R ![x, y]) (h : f y * g x = 3) (hgx : g x ≠ 0) :
    orderOf (reflection hf * reflection hg) = 6 := by
  refine orderOf_eq_of_pow_and_pow_div_prime
    (reflection_mul_reflection_pow_six_eq_one hf hg h) fun p hp hpd ↦ ?_
  have hp' : p = 2 ∨ p = 3 := by
    rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 2 * 3 from hpd) with h' | h'
    · exact .inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
    · exact .inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h')
  intro hpow
  rcases hp' with rfl | rfl
  · -- `(r₁ r₂)³ = 1` fails on the `x`-coefficient `S₃(1) + S₂(1) = -1`.
    have := (eval_S_eq_of_pow_eq_one hxy (n := 3) hpow).1
    have h₃ : (S R 3).eval (1 : R) = -1 := by
      have h₃' : S R (3 : ℤ) = Polynomial.X * S R 2 - S R 1 := by
        simpa using S_add_two R (1 : ℤ)
      simp [h₃', S_one, S_two]
    norm_num [h, h₃, S_two] at this
    exact (two_ne_zero : (2 : R) ≠ 0) (by linear_combination -this)
  · -- `(r₁ r₂)² = 1` fails on the `y`-coefficient `-S₁(1) g x = -g x`.
    have := (eval_S_eq_of_pow_eq_one hxy (n := 2) hpow).2
    norm_num [h, S_one] at this
    exact hgx this

/-- **Two reflections with Cartan product at least `4` generate an infinite dihedral group**:
if the vectors are linearly independent and `f y * g x` is the image of an integer `c ≥ 4`, in a
ring of characteristic zero, the product `r₁ r₂` has infinite order. For `c = 4` it is a shear,
and for `c > 4` a hyperbolic transformation. -/
theorem orderOf_reflection_mul_reflection_eq_zero [CharZero R]
    (hxy : LinearIndependent R ![x, y]) {c : ℤ} (h : f y * g x = c) (hc : 4 ≤ c) :
    orderOf (reflection hf * reflection hg) = 0 := by
  refine orderOf_eq_zero_iff'.mpr fun n hn hpow ↦ ?_
  have key := (eval_S_eq_of_pow_eq_one hxy hpow).1
  -- Transport the coefficient identity to the integers, where the growth bound applies.
  have hcast (k : ℤ) : (S R k).eval (f y * g x - 2) = (((S ℤ k).eval (c - 2) : ℤ) : R) := by
    rw [h, ← map_S (Int.castRingHom R), Polynomial.eval_map,
      show (c : R) - 2 = Int.castRingHom R (c - 2) by simp, Polynomial.eval₂_hom, eq_intCast]
  rw [hcast, hcast] at key
  have key' : (S ℤ n).eval (c - 2) + (S ℤ (n - 1)).eval (c - 2) = 1 := by exact_mod_cast key
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have ht : (2 : ℤ) ≤ c - 2 := by linarith
  have h₁ := natCast_add_one_le_eval_S ht (m + 1)
  have h₂ := natCast_add_one_le_eval_S ht m
  push_cast at key' h₁
  rw [add_sub_cancel_right] at key'
  linarith [(Nat.cast_nonneg m : (0 : ℤ) ≤ m)]

end Pair

end Module
