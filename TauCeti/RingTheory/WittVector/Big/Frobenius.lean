/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Big.Basic

import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.MvPolynomial.Counit
import TauCeti.RingTheory.MvPolynomial.Expand

/-!
# Big Witt Frobenius

The Frobenius `F_n : W_S(R) → W_{S/n}(R)` shifts ghost components by multiplication
of the index by `n`. Integral universal polynomials construct it over every commutative
ring, including rings with torsion. It commutes with coefficient maps and restriction.

## References

* L. Hesselholt, *The big de Rham–Witt complex*, Acta Math. 214 (2015), Lemma 1.4.
-/

public section

noncomputable section

namespace TauCeti.BigWittVector

open BigWitt _root_.MvPolynomial Function

variable {S T : TruncationSet} {R R' : Type*} [CommRing R] [CommRing R']

private theorem exists_frobeniusPolynomial (S : TruncationSet) (n : ℕ) :
    ∃ a : ℕ → MvPolynomial ℕ ℤ, ∀ k ∈ S / n,
      ghostPolynomial k a = ghostPolynomial (n * k) X := by
  have hφ : ∀ p : ℕ, p.Prime → ∀ a : MvPolynomial ℕ ℤ,
      (expand p : _ →ₐ[ℤ] _).toRingHom a - a ^ p ∈ Ideal.span {(p : MvPolynomial ℕ ℤ)} :=
    fun p hp a ↦ have := Fact.mk hp; Ideal.mem_span_singleton.2 (natCast_dvd_expand_sub_pow p a)
  refine (ghost_image (S / n) (fun p ↦ (expand p : _ →ₐ[ℤ] _).toRingHom)
    (fun p hp _ ↦ hφ p hp) _).2 fun p hp k hk hpk ↦ ?_
  have hle : multiplicity p k ≤ multiplicity p (n * k) :=
    (Nat.finiteMultiplicity_iff.2 ⟨hp.ne_one, S.pos_of_mem hk⟩).le_multiplicity_of_pow_dvd
      ((pow_multiplicity_dvd p k).trans (dvd_mul_left k n))
  rw [← Nat.mul_div_assoc n hpk]
  exact Ideal.mem_span_singleton.2 ((pow_dvd_pow _ hle).trans
    (Ideal.mem_span_singleton.1
      (ghostPolynomial_sub_map_ghostPolynomial_div_mem hp _ (hφ p hp) (n * k) X)))

private def frobeniusFun (n : ℕ) (x : BigWittVector S R) : BigWittVector (S / n) R :=
  mk' fun k ↦ aeval x.coeff ((exists_frobeniusPolynomial S n).choose k)

private theorem ghost_frobeniusFun (n : ℕ) (x : BigWittVector S R) (k : S / n) :
    ghostMap (frobeniusFun n x) k = ghostMap x ⟨n * k, k.property⟩ := by
  rw [ghostMap_apply, ghostMap_apply]
  refine (ghostPolynomial_congr fun d hd ↦
    coeff_mk'_of_mem _ ((S / n).mem_of_dvd k.property hd)).trans ?_
  have h := congrArg (aeval x.coeff) ((exists_frobeniusPolynomial S n).choose_spec k k.property)
  simpa only [map_ghostPolynomial, Function.comp_def, aeval_X] using h

private theorem frobeniusFun_map (n : ℕ) (f : R →+* R') (x : BigWittVector S R) :
    frobeniusFun n (map f x) = map f (frobeniusFun n x) := by
  ext k
  by_cases hk : k ∈ S / n
  · simp only [frobeniusFun, coeff_mk'_of_mem _ hk, coeff_map]
    rw [show (map f x).coeff = fun k ↦ f (x.coeff k) from funext (coeff_map f x)]
    exact (comp_aeval_apply x.coeff f.toIntAlgHom
      ((exists_frobeniusPolynomial S n).choose k)).symm
  · simp [coeff_eq_zero_of_notMem _ k hk]

private theorem polynomial_ghost_injective {ι : Type*} {T : TruncationSet} :
    Injective (ghostMap : BigWittVector T (MvPolynomial ι ℤ) →+* _) :=
  ghostMap_injective fun _ _ hp ↦ .of_ne_zero (Nat.cast_ne_zero.2 hp.ne_zero)

private theorem frobeniusFun_one (n : ℕ) : frobeniusFun n (1 : BigWittVector S R) = 1 := by
  have h : frobeniusFun n (1 : BigWittVector S (MvPolynomial R ℤ)) = 1 := by
    apply polynomial_ghost_injective
    ext k
    simp [ghost_frobeniusFun]
  have := congrArg (map (counit R)) h
  simpa only [map_one, ← frobeniusFun_map] using this

private theorem frobeniusFun_add (n : ℕ) (x y : BigWittVector S R) :
    frobeniusFun n (x + y) = frobeniusFun n x + frobeniusFun n y := by
  obtain ⟨a, rfl⟩ := map_surjective (counit R) (counit_surjective R) x
  obtain ⟨b, rfl⟩ := map_surjective (counit R) (counit_surjective R) y
  have h : frobeniusFun n (a + b) = frobeniusFun n a + frobeniusFun n b := by
    apply polynomial_ghost_injective
    ext k
    simp [ghost_frobeniusFun]
  calc
    _ = map (counit R) (frobeniusFun n (a + b)) := by
      rw [← map_add, frobeniusFun_map]
    _ = map (counit R) (frobeniusFun n a + frobeniusFun n b) := congrArg _ h
    _ = _ := by rw [map_add, frobeniusFun_map, frobeniusFun_map]

private theorem frobeniusFun_mul (n : ℕ) (x y : BigWittVector S R) :
    frobeniusFun n (x * y) = frobeniusFun n x * frobeniusFun n y := by
  obtain ⟨a, rfl⟩ := map_surjective (counit R) (counit_surjective R) x
  obtain ⟨b, rfl⟩ := map_surjective (counit R) (counit_surjective R) y
  have h : frobeniusFun n (a * b) = frobeniusFun n a * frobeniusFun n b := by
    apply polynomial_ghost_injective
    ext k
    simp [ghost_frobeniusFun]
  calc
    _ = map (counit R) (frobeniusFun n (a * b)) := by
      rw [← map_mul, frobeniusFun_map]
    _ = map (counit R) (frobeniusFun n a * frobeniusFun n b) := congrArg _ h
    _ = _ := by rw [map_mul, frobeniusFun_map, frobeniusFun_map]

/-- The big Witt Frobenius, characterized by `w_k(F_n(x)) = w_{n*k}(x)`. -/
def frobenius (n : ℕ) : BigWittVector S R →+* BigWittVector (S / n) R where
  toFun := frobeniusFun n
  map_zero' := by
    have h : frobeniusFun n (0 : BigWittVector S R) =
        frobeniusFun n 0 + frobeniusFun n 0 := by
      simpa only [add_zero] using frobeniusFun_add n (0 : BigWittVector S R) 0
    exact (add_left_cancel ((add_zero _).trans h)).symm
  map_one' := frobeniusFun_one n
  map_add' := frobeniusFun_add n
  map_mul' := frobeniusFun_mul n

/-- Frobenius shifts the index of each ghost component. -/
@[simp]
theorem ghostMap_frobenius (n : ℕ) (x : BigWittVector S R) (k : S / n) :
    ghostMap (frobenius n x) k = ghostMap x ⟨n * k, k.property⟩ :=
  ghost_frobeniusFun n x k

/-- Frobenius commutes with coefficient homomorphisms. -/
@[simp]
theorem frobenius_map (n : ℕ) (f : R →+* R') (x : BigWittVector S R) :
    frobenius n (map f x) = map f (frobenius n x) :=
  frobeniusFun_map n f x

/-- Frobenius commutes with restriction to smaller truncation sets. -/
theorem frobenius_restrict (n : ℕ) (h : T ≤ S) (x : BigWittVector S R) :
    frobenius n (restrict h x) =
      restrict (TruncationSet.div_le_div h n) (frobenius n x) := by
  obtain ⟨a, rfl⟩ := map_surjective (counit R) (counit_surjective R) x
  have hpoly : frobenius n (restrict h a) =
      restrict (TruncationSet.div_le_div h n) (frobenius n a) := by
    apply polynomial_ghost_injective
    ext k
    simp
  have hmap := DFunLike.congr_fun (map_comp_restrict h (counit R)) a
  have hdiv := DFunLike.congr_fun
    (map_comp_restrict (TruncationSet.div_le_div h n) (counit R)) (frobenius n a)
  simp only [RingHom.comp_apply] at hmap hdiv
  simpa only [← frobenius_map, hmap, hdiv] using congrArg (map (counit R)) hpoly

/-- Frobenius at index one is the identity, with its target presented as `S / 1`. -/
@[simp]
theorem frobenius_one (x : BigWittVector S R) :
    frobenius 1 x = restrict (le_of_eq (TruncationSet.div_one S)) x := by
  obtain ⟨a, rfl⟩ := map_surjective (counit R) (counit_surjective R) x
  have h : frobenius 1 a = restrict (le_of_eq (TruncationSet.div_one S)) a := by
    apply polynomial_ghost_injective
    ext k
    simp
  have hmap := DFunLike.congr_fun
    (map_comp_restrict (le_of_eq (TruncationSet.div_one S)) (counit R)) a
  simp only [RingHom.comp_apply] at hmap
  simpa only [← frobenius_map, hmap] using congrArg (map (counit R)) h

/-- Successive Frobenius maps multiply their indices. -/
theorem frobenius_frobenius (n k : ℕ) (x : BigWittVector S R) :
    frobenius k (frobenius n x) =
      restrict (le_of_eq (TruncationSet.div_div S n k)) (frobenius (n * k) x) := by
  obtain ⟨a, rfl⟩ := map_surjective (counit R) (counit_surjective R) x
  have h : frobenius k (frobenius n a) =
      restrict (le_of_eq (TruncationSet.div_div S n k)) (frobenius (n * k) a) := by
    apply polynomial_ghost_injective
    ext i
    simp [mul_assoc]
  have hmap := DFunLike.congr_fun
    (map_comp_restrict (le_of_eq (TruncationSet.div_div S n k)) (counit R))
      (frobenius (n * k) a)
  simp only [RingHom.comp_apply] at hmap
  simpa only [← frobenius_map, hmap] using congrArg (map (counit R)) h

/-- The first coordinate of Frobenius is the shifted ghost component. -/
theorem coeff_frobenius_one (n : ℕ) (hn : n ∈ S) (x : BigWittVector S R) :
    (frobenius n x).coeff 1 = ghostPolynomial n x.coeff := by
  have h := ghostMap_frobenius n x ⟨1, (TruncationSet.one_mem_div_iff).2 hn⟩
  simpa only [ghostMap_apply, ghostPolynomial_one, Nat.mul_one] using h

/-- At index zero the target truncation set is empty. -/
@[simp]
theorem frobenius_zero (x : BigWittVector S R) : frobenius 0 x = 0 := by
  have : Subsingleton (BigWittVector (S / 0) R) := by
    rw [TruncationSet.div_zero]
    infer_instance
  exact Subsingleton.elim _ _

end TauCeti.BigWittVector
