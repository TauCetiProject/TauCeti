/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Cyclotomic.Separable
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

/-- Evaluation at the power of a chosen primitive root labelled by a unit modulo `n`. -/
noncomputable def cyclotomicEval
    (hζ : (cyclotomic n R).IsRoot ζ) (a : (ZMod n)ˣ) :
    AdjoinRoot (cyclotomic n R) →ₐ[R] R :=
  AdjoinRoot.liftAlgHom _ (AlgHom.id R R) (ζ ^ (a : ZMod n).val)
    (by
      simpa only [AlgHom.id_toRingHom, eval₂_id] using
        (isRoot_cyclotomic_pow_of_coprime hζ (ZMod.val_coe_unit_coprime a)).eq_zero)

/-- Evaluation sends the universal primitive root to the labelled power of `ζ`. -/
@[simp]
theorem cyclotomicEval_root
    (hζ : (cyclotomic n R).IsRoot ζ) (a : (ZMod n)ˣ) :
    cyclotomicEval hζ a (AdjoinRoot.root (cyclotomic n R)) = ζ ^ (a : ZMod n).val := by
  rw [cyclotomicEval, AdjoinRoot.liftAlgHom_root]

variable [NeZero n]

/-- A chosen primitive root splits its cyclotomic algebra by evaluation at all primitive
powers. The statement holds over arbitrary commutative rings with `n` invertible. -/
theorem bijective_pi_cyclotomicEval (hn : IsUnit (n : R))
    (hζ : (cyclotomic n R).IsRoot ζ) :
    Function.Bijective (AlgHom.pi (cyclotomicEval hζ)) := by
  classical
  rcases subsingleton_or_nontrivial R with _ | _
  · have : Subsingleton (AdjoinRoot (cyclotomic n R)) := Module.subsingleton R _
    exact Function.bijective_of_subsingleton' _
  apply AdjoinRoot.bijective_pi_of_isUnit_sub (cyclotomic.monic n R)
    (by simp [natDegree_cyclotomic, ZMod.card_units_eq_totient]) (cyclotomicEval hζ)
  intro i j hij
  simp only [cyclotomicEval_root]
  apply isUnit_pow_sub_pow_of_isRoot_cyclotomic hn hζ (ZMod.val_lt _) (ZMod.val_lt _)
  intro h
  exact hij (Units.ext (ZMod.val_injective n h.symm))

/-- The splitting of the primitive-root algebra associated to a chosen primitive root.
The factors are labelled by units modulo `n`, not by an arbitrary enumeration. -/
noncomputable def adjoinRootCyclotomicEquivPi (hn : IsUnit (n : R))
    (hζ : (cyclotomic n R).IsRoot ζ) :
    AdjoinRoot (cyclotomic n R) ≃ₐ[R] ((ZMod n)ˣ → R) :=
  AlgEquiv.ofBijective (AlgHom.pi (cyclotomicEval hζ)) (bijective_pi_cyclotomicEval hn hζ)

/-- The splitting is evaluation in each labelled factor. -/
@[simp]
theorem adjoinRootCyclotomicEquivPi_apply (hn : IsUnit (n : R))
    (hζ : (cyclotomic n R).IsRoot ζ) (x : AdjoinRoot (cyclotomic n R)) (a : (ZMod n)ˣ) :
    adjoinRootCyclotomicEquivPi hn hζ x a = cyclotomicEval hζ a x :=
  (rfl)

/-- Each coordinate of the inverse splitting recovers the prescribed value. -/
@[simp]
theorem cyclotomicEval_adjoinRootCyclotomicEquivPi_symm (hn : IsUnit (n : R))
    (hζ : (cyclotomic n R).IsRoot ζ) (x : (ZMod n)ˣ → R) (a : (ZMod n)ˣ) :
    cyclotomicEval hζ a ((adjoinRootCyclotomicEquivPi hn hζ).symm x) = x a :=
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
