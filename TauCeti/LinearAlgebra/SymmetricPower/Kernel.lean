/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricPower.Coordinates

/-!
# The kernel of the symmetric-square action

On a free module over a commutative semiring, an endomorphism acting trivially on the symmetric
square is a scalar whose square is one. Mixed symmetric products detect the off-diagonal entries
without cancelling a factor of two, so the argument also works over nonreduced coefficients.
-/

public section

open scoped TensorProduct

namespace SymmetricPower

universe u

/-- Scaling a linear map scales its symmetric power by the corresponding power. -/
@[simp]
theorem map_smul {R ι : Type u} {M N : Type*} [CommSemiring R] [Fintype ι]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] (a : R) (f : M →ₗ[R] N) :
    map (ι := ι) (a • f) = a ^ Fintype.card ι • map (ι := ι) f := by
  apply SymmetricPower.ext
  intro m
  simpa only [map_tprod, LinearMap.smul_apply, RingHom.id_apply, Finset.prod_const,
    Finset.card_univ] using
    (tprod R).map_smul_univ (fun _ : ι => a) (fun i => f (m i))

variable {R : Type} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The symmetric square of an endomorphism of a free module is the identity exactly when the
endomorphism is multiplication by a square root of one. -/
theorem map_fin_two_eq_id_iff {κ : Type*} (b : Module.Basis κ R M)
    (f : M →ₗ[R] M) : map (ι := Fin 2) f = LinearMap.id ↔
      ∃ a : R, a ^ 2 = 1 ∧ f = a • LinearMap.id := by
  classical
  refine ⟨fun h => ?_, ?_⟩
  · let a (i : κ) := b.repr (f (b i)) i
    have hcoeff (i k j : κ) : b.repr (f (b i)) j * b.repr (f (b k)) j =
        b.repr (b i) j * b.repr (b k) j := by
      let p : Fin 2 → κ := ![i, k]
      have he := LinearMap.congr_fun h (⨂ₛ[R] t, b (p t))
      have hc := congrArg (fun x => (b.symmetricPower 2).repr x (Sym.ofFn fun _ => j)) he
      simpa only [map_tprod, LinearMap.id_apply,
        Module.Basis.symmetricPower_repr_tprod_apply_ofFn_const, Fin.prod_univ_two,
        p, Matrix.cons_val_zero, Matrix.cons_val_one] using hc
    have hself (j : κ) : a j * a j = 1 := by
      simpa [a] using hcoeff j j j
    have hdiag (i : κ) : f (b i) = a i • b i := by
      apply b.repr.injective
      ext j
      by_cases hij : i = j
      · subst j
        simp [a]
      · have hz : b.repr (f (b i)) j * a j = 0 := by
          simpa [a, Module.Basis.repr_self, Finsupp.single_apply, hij, eq_comm] using hcoeff i j j
        have hj := congrArg (· * a j) hz
        rw [mul_assoc, hself, mul_one, zero_mul] at hj
        simp [hj, hij, eq_comm]
    have hmul (i j : κ) : a i * a j = 1 := by
      let p : Fin 2 → κ := ![i, j]
      have he := LinearMap.congr_fun h (⨂ₛ[R] t, b (p t))
      simp only [map_tprod, LinearMap.id_apply, hdiag, (tprod R).map_smul_univ] at he
      let s := Sym.ofFn p
      have ht : (⨂ₛ[R] t, b (p t)) = b.symmetricPower 2 s := by
        rw [Module.Basis.symmetricPower_apply, tprodOfSym_ofFn]
      rw [ht] at he
      simpa only [LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_single,
        Finsupp.single_eq_same, smul_eq_mul, mul_one, RingHom.id_apply, Fin.prod_univ_two,
        p, Matrix.cons_val_zero, Matrix.cons_val_one] using
        congrArg (fun x => (b.symmetricPower 2).repr x s) he
    cases isEmpty_or_nonempty κ with
    | inl _ => exact ⟨1, one_pow _, b.ext fun i => isEmptyElim i⟩
    | inr hn =>
      obtain ⟨i⟩ := hn
      refine ⟨a i, by simpa [pow_two] using hmul i i, b.ext fun j => ?_⟩
      have heq : a j = a i := by
        calc
          a j = (a i * a i) * a j := by rw [hmul i i, one_mul]
          _ = a i := by rw [mul_assoc, hmul i j, mul_one]
      simp [hdiag, heq]
  · rintro ⟨a, ha, rfl⟩
    rw [map_smul, Fintype.card_fin, ha, one_smul, map_id]

end SymmetricPower
