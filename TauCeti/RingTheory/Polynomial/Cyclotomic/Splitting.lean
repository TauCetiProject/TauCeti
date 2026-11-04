/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Cyclotomic.Separable
public import Mathlib.Data.ZMod.Basic
import TauCeti.RingTheory.AdjoinRoot.Splitting
import TauCeti.RingTheory.AdjoinRoot.Basic

/-!
# Splitting the algebra of primitive roots of unity

If `n` is invertible and `ζ` is a root of `Φ_n` in a commutative ring `R`, evaluation at
`ζ ^ a`, for `a ∈ (ℤ/nℤ)ˣ`, identifies `R[X]/(Φ_n)` with a product of copies of `R`.
Thus adjoining a primitive root splits the finite étale scheme of primitive roots.
This is the algebraic splitting used to separate fixed Weil-pairing fibres.

A root of `Φ_n`, not just an element of abstract order `n`, is required: over a
disconnected ring the latter need not have order `n` on every component. No reducedness,
connectedness or field hypothesis is imposed on `R`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §§3.1 and 3.7.
-/

public section

open scoped TensorProduct

namespace Polynomial

variable {R : Type*} [CommRing R] {n : ℕ} {ζ : R}

/-- Distinct powers, with exponents less than `n`, of a cyclotomic root have unit
difference when `n` is invertible. Distinctness alone would not suffice over a ring. -/
theorem isUnit_pow_sub_pow_of_isRoot_cyclotomic (hn : IsUnit (n : R))
    (hζ : (cyclotomic n R).IsRoot ζ) {i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    IsUnit (ζ ^ i - ζ ^ j) := by
  by_contra hu
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
  have hp := ((isRoot_cyclotomic_iff_forall_isPrimitiveRoot hn).mp hζ).2 m hm.isPrime
  have he : (Ideal.Quotient.mk m ζ) ^ i = (Ideal.Quotient.mk m ζ) ^ j := by
    simpa [sub_eq_zero] using Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  exact hij (hp.pow_inj hi hj he)

/-- A power of a cyclotomic root with exponent coprime to `n` is again a cyclotomic
root when `n` is invertible, including over nonreduced bases. -/
theorem isRoot_cyclotomic_pow_of_coprime (hn : IsUnit (n : R))
    (hζ : (cyclotomic n R).IsRoot ζ) {a : ℕ} (ha : a.Coprime n) :
    (cyclotomic n R).IsRoot (ζ ^ a) := by
  obtain ⟨hpow, hp⟩ := (isRoot_cyclotomic_iff_forall_isPrimitiveRoot hn).mp hζ
  apply (isRoot_cyclotomic_iff_forall_isPrimitiveRoot hn).mpr
  refine ⟨?_, fun m hm ↦ ?_⟩
  · rw [← pow_mul, Nat.mul_comm, pow_mul, hpow, one_pow]
  · simpa only [map_pow] using (hp m hm).pow_of_coprime a ha

/-- Evaluation at the power of a chosen primitive root labelled by a unit modulo `n`. -/
noncomputable def cyclotomicEval (hn : IsUnit (n : R))
    (hζ : (cyclotomic n R).IsRoot ζ) (a : (ZMod n)ˣ) :
    AdjoinRoot (cyclotomic n R) →ₐ[R] R :=
  AdjoinRoot.liftAlgHom _ (AlgHom.id R R) (ζ ^ (a : ZMod n).val)
    (by
      simpa only [AlgHom.id_toRingHom, eval₂_id] using
        (isRoot_cyclotomic_pow_of_coprime hn hζ (ZMod.val_coe_unit_coprime a)).eq_zero)

/-- Evaluation sends the universal primitive root to the labelled power of `ζ`. -/
@[simp]
theorem cyclotomicEval_root (hn : IsUnit (n : R))
    (hζ : (cyclotomic n R).IsRoot ζ) (a : (ZMod n)ˣ) :
    cyclotomicEval hn hζ a (AdjoinRoot.root (cyclotomic n R)) = ζ ^ (a : ZMod n).val := by
  rw [cyclotomicEval, AdjoinRoot.liftAlgHom_root]

variable [NeZero n]

/-- A chosen primitive root splits its cyclotomic algebra by evaluation at all primitive
powers. The statement holds over arbitrary commutative rings with `n` invertible. -/
theorem bijective_pi_cyclotomicEval (hn : IsUnit (n : R))
    (hζ : (cyclotomic n R).IsRoot ζ) :
    Function.Bijective (AlgHom.pi (cyclotomicEval hn hζ)) := by
  classical
  rcases subsingleton_or_nontrivial R with _ | _
  · have : Subsingleton (AdjoinRoot (cyclotomic n R)) := Module.subsingleton R _
    exact Function.bijective_of_subsingleton' _
  let e : Fin (cyclotomic n R).natDegree ≃ (ZMod n)ˣ :=
    Fintype.equivOfCardEq (by simp [natDegree_cyclotomic, ZMod.card_units_eq_totient])
  have hb := AdjoinRoot.bijective_pi_of_isUnit_sub (cyclotomic.monic n R)
    (fun i ↦ cyclotomicEval hn hζ (e i)) (fun i j hij ↦ ?_)
  · have he : (AlgHom.pi (fun i ↦ cyclotomicEval hn hζ (e i)) :
        AdjoinRoot (cyclotomic n R) → Fin (cyclotomic n R).natDegree → R) =
        (Equiv.piCongrLeft' (fun _ : (ZMod n)ˣ ↦ R) e.symm) ∘
          AlgHom.pi (cyclotomicEval hn hζ) := by
      rfl
    rw [he] at hb
    exact (Equiv.comp_bijective _ _).mp hb
  · simp only [cyclotomicEval_root]
    apply isUnit_pow_sub_pow_of_isRoot_cyclotomic hn hζ (ZMod.val_lt _) (ZMod.val_lt _)
    intro h
    exact hij (e.injective (Units.ext (ZMod.val_injective n h.symm)))

/-- The splitting of the primitive-root algebra associated to a chosen primitive root.
The factors are labelled by units modulo `n`, not by an arbitrary enumeration. -/
noncomputable def adjoinRootCyclotomicEquivPi (hn : IsUnit (n : R))
    (hζ : (cyclotomic n R).IsRoot ζ) :
    AdjoinRoot (cyclotomic n R) ≃ₐ[R] ((ZMod n)ˣ → R) :=
  AlgEquiv.ofBijective (AlgHom.pi (cyclotomicEval hn hζ)) (bijective_pi_cyclotomicEval hn hζ)

/-- The splitting is evaluation in each labelled factor. -/
@[simp]
theorem adjoinRootCyclotomicEquivPi_apply (hn : IsUnit (n : R))
    (hζ : (cyclotomic n R).IsRoot ζ) (x : AdjoinRoot (cyclotomic n R)) (a : (ZMod n)ˣ) :
    adjoinRootCyclotomicEquivPi hn hζ x a = cyclotomicEval hn hζ a x :=
  (rfl)

/-- Each coordinate of the inverse splitting recovers the prescribed value. -/
@[simp]
theorem cyclotomicEval_adjoinRootCyclotomicEquivPi_symm (hn : IsUnit (n : R))
    (hζ : (cyclotomic n R).IsRoot ζ) (x : (ZMod n)ˣ → R) (a : (ZMod n)ˣ) :
    cyclotomicEval hn hζ a ((adjoinRootCyclotomicEquivPi hn hζ).symm x) = x a :=
  congrFun ((adjoinRootCyclotomicEquivPi hn hζ).apply_symm_apply x) a

section BaseChange

variable (R) {A : Type*} [CommRing A] [Algebra R A] {ξ : A}

/-- After any base change carrying a primitive root, the primitive-root algebra is a
product indexed by units modulo `n`. In particular this applies to base change along
`R → R[X]/(Φ_n)` itself when `n` is invertible in `R`. -/
noncomputable def cyclotomicBaseChangeEquivPi (hn : IsUnit (n : A))
    (hξ : (cyclotomic n A).IsRoot ξ) :
    (A ⊗[R] AdjoinRoot (cyclotomic n R)) ≃ₐ[A] ((ZMod n)ˣ → A) :=
  (AdjoinRoot.algebraTensorAlgEquiv A (cyclotomic n R)).trans <|
    (AdjoinRoot.algEquivOfEq A _ _ (map_cyclotomic n (algebraMap R A))).trans
      (adjoinRootCyclotomicEquivPi hn hξ)

/-- The base-changed splitting sends scalar multiples of the universal root to the
corresponding multiples of all primitive powers of the chosen root. -/
@[simp]
theorem cyclotomicBaseChangeEquivPi_tmul_root (hn : IsUnit (n : A))
    (hξ : (cyclotomic n A).IsRoot ξ) (x : A) (a : (ZMod n)ˣ) :
    cyclotomicBaseChangeEquivPi R hn hξ (x ⊗ₜ AdjoinRoot.root (cyclotomic n R)) a =
      x * ξ ^ (a : ZMod n).val := by
  have h : x ⊗ₜ[R] AdjoinRoot.root (cyclotomic n R) =
      x • (1 ⊗ₜ[R] AdjoinRoot.root (cyclotomic n R)) := by
    simp [TensorProduct.smul_tmul']
  rw [h, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, cyclotomicBaseChangeEquivPi, AlgEquiv.trans_apply,
    AdjoinRoot.algebraTensorAlgEquiv_one_tmul_root, AdjoinRoot.algEquivOfEq_root,
    adjoinRootCyclotomicEquivPi_apply, cyclotomicEval_root]

end BaseChange

end Polynomial
