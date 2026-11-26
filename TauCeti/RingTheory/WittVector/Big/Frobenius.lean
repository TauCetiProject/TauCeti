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

universe u

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
    (Nat.finiteMultiplicity_iff.2
      ⟨hp.ne_one, S.pos_of_mem (TruncationSet.mem_div.mp hk)⟩).le_multiplicity_of_pow_dvd
      ((pow_multiplicity_dvd p k).trans (dvd_mul_left k n))
  rw [← Nat.mul_div_assoc n hpk]
  exact Ideal.mem_span_singleton.2 ((pow_dvd_pow _ hle).trans
    (Ideal.mem_span_singleton.1
      (ghostPolynomial_sub_map_ghostPolynomial_div_mem hp _ (hφ p hp) (n * k) X)))

private def frobeniusFun (n : ℕ) (x : BigWittVector S R) : BigWittVector (S / n) R :=
  mk' fun k ↦ aeval x.coeff ((exists_frobeniusPolynomial S n).choose k)

private theorem ghost_frobeniusFun (n : ℕ) (x : BigWittVector S R) (k : S / n) :
    ghostMap (frobeniusFun n x) k = ghostMap x ⟨n * k, TruncationSet.mem_div.mp k.property⟩ := by
  rw [ghostMap_apply, ghostMap_apply]
  refine (ghostPolynomial_congr fun d hd ↦
    coeff_mk'_of_mem _ ((S / n).mem_of_dvd k.property hd)).trans ?_
  have h := congrArg (aeval x.coeff) ((exists_frobeniusPolynomial S n).choose_spec k k.property)
  simpa only [map_ghostPolynomial, Function.comp_def, aeval_X] using h

private theorem frobeniusFun_map (n : ℕ) (f : R →+* R') (x : BigWittVector S R) :
    frobeniusFun n (map f x) = map f (frobeniusFun n x) := by
  ext k
  by_cases hk : k ∈ S / n
  · have hcoeff : (map f x).coeff = fun k ↦ f (x.coeff k) :=
      funext (coeff_map f x)
    simp only [frobeniusFun, coeff_mk'_of_mem _ hk, coeff_map, hcoeff]
    exact (comp_aeval_apply x.coeff f.toIntAlgHom
      ((exists_frobeniusPolynomial S n).choose k)).symm
  · simp [coeff_eq_zero_of_notMem _ k hk]

-- Ghosts determine the vectors over the integral polynomial ring, so their equality survives
-- specialization by evaluating each variable at the coefficient it names.
private theorem map_counit_eq_of_ghostMap_eq {x y : BigWittVector T (MvPolynomial R ℤ)}
    (h : ghostMap x = ghostMap y) : map (counit R) x = map (counit R) y :=
  congrArg (map (counit R))
    (ghostMap_injective (fun _ _ hp ↦ .of_ne_zero (Nat.cast_ne_zero.2 hp.ne_zero)) h)

-- A surjective parametrization lifts all inputs at once, including pairs of Witt vectors.
-- Naturality then specializes an identity proved by comparing integral polynomial ghosts.
private theorem eq_of_ghostMap_eq_of_surjective {D₀ D : Type*}
    (π : D₀ → D) (hπ : Surjective π)
    {P : D → Prop} (f₀ g₀ : D₀ → BigWittVector T (MvPolynomial R ℤ))
    (hspecialize : ∀ a, map (counit R) (f₀ a) = map (counit R) (g₀ a) → P (π a))
    (hghost : ∀ a, ghostMap (f₀ a) = ghostMap (g₀ a)) : ∀ a, P a :=
  hπ.forall.mpr fun a ↦ hspecialize a (map_counit_eq_of_ghostMap_eq (hghost a))

private theorem frobeniusFun_one (n : ℕ) : frobeniusFun n (1 : BigWittVector S R) = 1 := by
  simpa only [map_one, ← frobeniusFun_map] using
    (map_counit_eq_of_ghostMap_eq (x := frobeniusFun n (1 : BigWittVector S (MvPolynomial R ℤ)))
      (y := 1) (by ext k; simp [ghost_frobeniusFun]))

-- The same operation commutes with both ghost components and coefficient specialization.
private theorem frobeniusFun_map₂ {A : Type u} [CommRing A] (n : ℕ)
    (op : ∀ {B : Type u} [CommRing B], B → B → B)
    (hop : ∀ {B C : Type u} [CommRing B] [CommRing C] (f : B →+* C) (x y : B),
      f (op x y) = op (f x) (f y))
    (x y : BigWittVector S A) :
    frobeniusFun n (op x y) = op (frobeniusFun n x) (frobeniusFun n y) := by
  have hop_ghost {U : TruncationSet} (a b : BigWittVector U (MvPolynomial A ℤ)) (k : U) :
      ghostMap (op a b) k = op (ghostMap a k) (ghostMap b k) :=
    hop ((Pi.evalRingHom _ k).comp ghostMap) a b
  have hsurj := map_surjective (S := S) (counit A) (counit_surjective A)
  exact eq_of_ghostMap_eq_of_surjective _ (hsurj.prodMap hsurj)
    (P := fun a : BigWittVector S A × BigWittVector S A ↦
      frobeniusFun n (op a.1 a.2) = op (frobeniusFun n a.1) (frobeniusFun n a.2))
    (fun a ↦ frobeniusFun n (op a.1 a.2))
    (fun a ↦ op (frobeniusFun n a.1) (frobeniusFun n a.2))
    (fun a e ↦ by simpa only [hop, ← frobeniusFun_map, Prod.map_fst, Prod.map_snd] using e)
    (fun a ↦ by ext k; simp only [hop_ghost, ghost_frobeniusFun]) (x, y)

private theorem frobeniusFun_add (n : ℕ) (x y : BigWittVector S R) :
    frobeniusFun n (x + y) = frobeniusFun n x + frobeniusFun n y :=
  frobeniusFun_map₂ n (· + ·) map_add x y

private theorem frobeniusFun_mul (n : ℕ) (x y : BigWittVector S R) :
    frobeniusFun n (x * y) = frobeniusFun n x * frobeniusFun n y :=
  frobeniusFun_map₂ n (· * ·) map_mul x y

/-- The big Witt Frobenius, satisfying `w_k(F_n(x)) = w_{n*k}(x)`. -/
def frobenius (n : ℕ) : BigWittVector S R →+* BigWittVector (S / n) R :=
  RingHom.mk'
    { toFun := frobeniusFun n
      map_one' := frobeniusFun_one n
      map_mul' := frobeniusFun_mul n } (frobeniusFun_add n)

/-- Frobenius shifts the index of each ghost component. -/
@[simp]
theorem ghostMap_frobenius (n : ℕ) (x : BigWittVector S R) (k : S / n) :
    ghostMap (frobenius n x) k = ghostMap x ⟨n * k, TruncationSet.mem_div.mp k.property⟩ :=
  ghost_frobeniusFun n x k

/-- Frobenius commutes with coefficient homomorphisms. -/
@[simp]
theorem frobenius_map (n : ℕ) (f : R →+* R') (x : BigWittVector S R) :
    frobenius n (map f x) = map f (frobenius n x) :=
  frobeniusFun_map n f x

-- Lift the input along the polynomial counit and specialize the equality of the two outputs.
private theorem eq_of_ghostMap_eq_of_counit {A : Type u} [CommRing A]
    (f g : ∀ {B : Type u} [CommRing B], BigWittVector S B → BigWittVector T B)
    (hspecialize : ∀ a : BigWittVector S (MvPolynomial A ℤ),
      map (counit A) (f a) = map (counit A) (g a) → f (map (counit A) a) = g (map (counit A) a))
    (hghost : ∀ a : BigWittVector S (MvPolynomial A ℤ), ghostMap (f a) = ghostMap (g a))
    (x : BigWittVector S A) : f x = g x :=
  eq_of_ghostMap_eq_of_surjective _ (map_surjective (counit A) (counit_surjective A))
    (P := fun a ↦ f a = g a) f g hspecialize hghost x

/-- Frobenius commutes with restriction to smaller truncation sets. -/
theorem frobenius_restrict (n : ℕ) (h : T ≤ S) (x : BigWittVector S R) :
    frobenius n (restrict h x) =
      restrict (TruncationSet.div_le_div h n) (frobenius n x) :=
  eq_of_ghostMap_eq_of_counit (fun a ↦ frobenius n (restrict h a))
    (fun a ↦ restrict (TruncationSet.div_le_div h n) (frobenius n a))
    (fun a e ↦ by simpa only [← frobenius_map, map_restrict] using e)
    (fun a ↦ by ext k; simp) x

/-- Frobenius at index one is the identity, with its target presented as `S / 1`. -/
@[simp]
theorem frobenius_one (x : BigWittVector S R) :
    frobenius 1 x = restrict (le_of_eq (TruncationSet.div_one S)) x :=
  eq_of_ghostMap_eq_of_counit (fun a ↦ frobenius 1 a)
    (fun a ↦ restrict (le_of_eq (TruncationSet.div_one S)) a)
    (fun a e ↦ by simpa only [← frobenius_map, map_restrict] using e)
    (fun a ↦ by ext k; simp) x

/-- Successive Frobenius maps multiply their indices. -/
theorem frobenius_frobenius (n k : ℕ) (x : BigWittVector S R) :
    frobenius k (frobenius n x) =
      restrict (le_of_eq (TruncationSet.div_div S n k)) (frobenius (n * k) x) :=
  eq_of_ghostMap_eq_of_counit (fun a ↦ frobenius k (frobenius n a))
    (fun a ↦ restrict (le_of_eq (TruncationSet.div_div S n k)) (frobenius (n * k) a))
    (fun a e ↦ by simpa only [← frobenius_map, map_restrict] using e)
    (fun a ↦ by ext i; simp [mul_assoc]) x

/-- The first coordinate of Frobenius is the shifted ghost component. -/
@[simp]
theorem coeff_one_frobenius (n : ℕ) (hn : n ∈ S) (x : BigWittVector S R) :
    (frobenius n x).coeff 1 = ghostPolynomial n x.coeff := by
  have h := ghostMap_frobenius n x ⟨1, (TruncationSet.one_mem_div_iff).2 hn⟩
  simpa only [ghostMap_apply, ghostPolynomial_one, Nat.mul_one] using h

/-- Frobenius at index zero is zero because its target truncation set is empty. -/
@[simp]
theorem frobenius_zero (x : BigWittVector S R) : frobenius 0 x = 0 := by
  have : Subsingleton (BigWittVector (S / 0) R) := by
    rw [TruncationSet.div_zero]
    infer_instance
  exact Subsingleton.elim _ _

end TauCeti.BigWittVector
