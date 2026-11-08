/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Symmetric descent for the universal resolvent

Given a multivariable polynomial `Φ` over a commutative ring in finitely many formal roots, its
universal resolvent is the product of `X - Ψ` over the orbit of `Φ` under permutations of the
variables. Permuting the formal roots permutes these factors, so every coefficient of the product
is symmetric.

For `n` formal roots, the fundamental theorem of symmetric polynomials then gives a unique
polynomial whose coefficients specialize to the universal resolvent after sending the variables to
the elementary symmetric polynomials. Over `ℤ`, this is the integral orbit product used by a
resolvent specification.

## Main definitions

* `MvPolynomial.renameStabilizer`: the subgroup of permutations fixing an invariant.
* `MvPolynomial.renameOrbit`: the finite set of polynomials obtained by permuting the variables.
* `MvPolynomial.universalResolvent`: the product over the rename-orbit of an invariant.
* `TauCeti.esymmSubst`: substitution of the elementary symmetric polynomials for the variables.

## Main results

* `MvPolynomial.rename_eq_rename_iff`: two permutations give the same renaming exactly when
  their quotient stabilizes the polynomial.
* `MvPolynomial.card_renameOrbit`: the rename-orbit has size the index of the stabilizer.
* `MvPolynomial.renameOrbit_rename` and `MvPolynomial.universalResolvent_rename`: renaming an
  invariant does not change its orbit or universal resolvent.
* `MvPolynomial.universalResolvent_def`: the universal resolvent is the product of the linear
  factors attached to the orbit.
* `MvPolynomial.universalResolvent_map_rename`: the universal resolvent is invariant under
  renaming.
* `MvPolynomial.isSymmetric_universalResolvent_coeff`: all of its coefficients are
  symmetric.
* `TauCeti.esymmSubst_injective`: elementary-symmetric substitution is injective.
* `MvPolynomial.existsUnique_orbitProduct`: the universal resolvent descends uniquely
  through elementary-symmetric substitution.
* `MvPolynomial.monic_universalResolvent` and `MvPolynomial.natDegree_universalResolvent`: the
  universal resolvent is monic of degree the size of the orbit, and
  `MvPolynomial.monic_of_map_esymmSubst_eq`, `MvPolynomial.natDegree_of_map_esymmSubst_eq`
  transfer this to its expression in the elementary symmetric polynomials.
-/

public section

open Polynomial

namespace MvPolynomial

section Stabilizer

variable {σ R : Type*} [CommSemiring R]

/-- The stabilizer of a multivariable polynomial under permutation of its variables. -/
def renameStabilizer (Φ : MvPolynomial σ R) : Subgroup (Equiv.Perm σ) where
  carrier := {e | rename (⇑e) Φ = Φ}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [Equiv.Perm.coe_mul, ← rename_rename, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    conv_lhs => rw [← ha]
    simp [rename_rename]

/-- A permutation lies in the stabilizer exactly when renaming by it fixes the polynomial. -/
@[simp]
theorem mem_renameStabilizer {Φ : MvPolynomial σ R} {e : Equiv.Perm σ} :
    e ∈ renameStabilizer Φ ↔ rename (⇑e) Φ = Φ :=
  Iff.rfl

/-- Two permutations rename a polynomial identically exactly when their quotient stabilizes it. -/
theorem rename_eq_rename_iff (Φ : MvPolynomial σ R) (a b : Equiv.Perm σ) :
    rename (⇑a) Φ = rename (⇑b) Φ ↔ a⁻¹ * b ∈ renameStabilizer Φ := by
  rw [mem_renameStabilizer, ← (rename_injective _ a.injective).eq_iff (b := Φ), rename_rename,
    ← Equiv.Perm.coe_mul, mul_inv_cancel_left, eq_comm]

/-- A polynomial is symmetric exactly when its stabilizer is the whole symmetric group. -/
@[simp]
theorem renameStabilizer_eq_top_iff {Φ : MvPolynomial σ R} :
    renameStabilizer Φ = ⊤ ↔ Φ.IsSymmetric := by
  simp [Subgroup.eq_top_iff', IsSymmetric]

/-- The stabilizer of a renamed polynomial is the conjugate stabilizer. -/
@[simp]
theorem renameStabilizer_rename (e : Equiv.Perm σ) (Φ : MvPolynomial σ R) :
    renameStabilizer (rename (⇑e) Φ) = (renameStabilizer Φ).map (MulAut.conj e).toMonoidHom := by
  ext τ
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mul_assoc, ← rename_eq_rename_iff,
    mem_renameStabilizer, rename_rename, ← Equiv.Perm.coe_mul, eq_comm]

end Stabilizer

section Orbit

variable {σ R : Type*} [Finite σ] [CommSemiring R]

/-- The finite set of distinct polynomials obtained by permuting the variables of `Φ`. -/
noncomputable def renameOrbit (Φ : MvPolynomial σ R) : Finset (MvPolynomial σ R) :=
  (Set.finite_range fun e : Equiv.Perm σ => rename (⇑e) Φ).toFinset

/-- Membership in the rename-orbit is witnessed by a permutation of the variables. -/
@[simp]
theorem mem_renameOrbit (Φ Ψ : MvPolynomial σ R) :
    Ψ ∈ renameOrbit Φ ↔ ∃ e : Equiv.Perm σ, rename (⇑e) Φ = Ψ := by
  simp [renameOrbit]

/-- **Orbit–stabilizer for invariants.** The rename-orbit of `Φ` has as many elements as the
index of its stabilizer. -/
theorem card_renameOrbit (Φ : MvPolynomial σ R) :
    (renameOrbit Φ).card = (renameStabilizer Φ).index := by
  -- The action of permutations on polynomials by renaming the variables, whose stabilizer and
  -- orbit of `Φ` are `renameStabilizer Φ` and `renameOrbit Φ` by definition.
  let _ : MulAction (Equiv.Perm σ) (MvPolynomial σ R) :=
    { smul := fun e p => rename (⇑e) p
      one_smul := rename_id_apply
      mul_smul := fun a b p => (rename_rename (⇑b) (⇑a) p).symm }
  exact (Set.ncard_eq_toFinset_card _ _).symm.trans
    (MulAction.index_stabilizer (Equiv.Perm σ) Φ).symm

/-- A renamed invariant has the same rename-orbit. -/
@[simp]
theorem renameOrbit_rename (e : Equiv.Perm σ) (Φ : MvPolynomial σ R) :
    renameOrbit (rename (⇑e) Φ) = renameOrbit Φ := by
  ext Ψ
  simp only [mem_renameOrbit, rename_rename, ← Equiv.Perm.coe_mul]
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨τ * e, rfl⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨τ * e⁻¹, by rw [inv_mul_cancel_right]⟩

/-- Renaming the variables permutes the rename-orbit. -/
private theorem image_rename_renameOrbit [DecidableEq (MvPolynomial σ R)]
    (Φ : MvPolynomial σ R) (e : Equiv.Perm σ) :
    (renameOrbit Φ).image (rename (⇑e)) = renameOrbit Φ := by
  ext Ψ
  simp only [Finset.mem_image, mem_renameOrbit]
  constructor
  · rintro ⟨-, ⟨τ, rfl⟩, rfl⟩
    exact ⟨e * τ, by rw [Equiv.Perm.coe_mul, rename_rename]⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨_, ⟨e⁻¹ * τ, rfl⟩, by rw [rename_rename, ← Equiv.Perm.coe_mul, mul_inv_cancel_left]⟩

end Orbit

section Resolvent

variable {σ R : Type*} [Finite σ] [CommRing R]

/-- The universal resolvent of `Φ`, formed over the orbit obtained by permuting its variables. -/
noncomputable def universalResolvent (Φ : MvPolynomial σ R) : (MvPolynomial σ R)[X] :=
  ∏ Ψ ∈ renameOrbit Φ, (Polynomial.X - Polynomial.C Ψ)

/-- The universal resolvent is the product of the monic linear factors `X - Ψ` attached to the
elements of the rename-orbit. -/
theorem universalResolvent_def (Φ : MvPolynomial σ R) :
    universalResolvent Φ = ∏ Ψ ∈ renameOrbit Φ, (Polynomial.X - Polynomial.C Ψ) := (rfl)

/-- A renamed invariant has the same universal resolvent. -/
@[simp]
theorem universalResolvent_rename (e : Equiv.Perm σ) (Φ : MvPolynomial σ R) :
    universalResolvent (rename (⇑e) Φ) = universalResolvent Φ := by
  rw [universalResolvent_def, universalResolvent_def, renameOrbit_rename]

/-- The universal resolvent is monic, being a product of monic linear factors. -/
theorem monic_universalResolvent (Φ : MvPolynomial σ R) : (universalResolvent Φ).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- The universal resolvent has degree the number of elements of the rename-orbit. -/
@[simp]
theorem natDegree_universalResolvent [Nontrivial R] (Φ : MvPolynomial σ R) :
    (universalResolvent Φ).natDegree = (renameOrbit Φ).card := by
  rw [universalResolvent_def, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp

/-- Permuting the formal roots leaves the universal resolvent unchanged. -/
@[simp]
theorem universalResolvent_map_rename (Φ : MvPolynomial σ R) (e : Equiv.Perm σ) :
    (universalResolvent Φ).map (rename (R := R) ⇑e : MvPolynomial σ R →+* MvPolynomial σ R) =
      universalResolvent Φ := by
  classical
  rw [universalResolvent_def, Polynomial.map_prod]
  conv_rhs => rw [← image_rename_renameOrbit Φ e,
    Finset.prod_image fun _ _ _ _ h => rename_injective _ e.injective h]
  simp

/-- Every coefficient of the universal resolvent is symmetric in the formal roots. -/
theorem isSymmetric_universalResolvent_coeff (Φ : MvPolynomial σ R) (k : ℕ) :
    ((universalResolvent Φ).coeff k).IsSymmetric := fun e => by
  simpa only [Polynomial.coeff_map, RingHom.coe_coe] using
    congrArg (Polynomial.coeff · k) (universalResolvent_map_rename Φ e)

end Resolvent

end MvPolynomial

namespace TauCeti

section esymmSubst

variable {R : Type*}

/-- The substitution sending variable `i` to the elementary symmetric polynomial `e_(i+1)`. -/
noncomputable def esymmSubst [CommSemiring R] (n : ℕ) :
    MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R :=
  (MvPolynomial.aeval fun i : Fin n => MvPolynomial.esymm (Fin n) R ((i : ℕ) + 1)).toRingHom

/-- Elementary-symmetric substitution sends `X i` to `e_(i+1)`. -/
@[simp]
theorem esymmSubst_X [CommSemiring R] (n : ℕ) (i : Fin n) :
    esymmSubst n (MvPolynomial.X i) = MvPolynomial.esymm (Fin n) R ((i : ℕ) + 1) := by
  simp [esymmSubst]

/-- Elementary-symmetric substitution agrees with Mathlib's fundamental-theorem map. -/
theorem esymmSubst_apply [CommSemiring R] (n : ℕ) (p : MvPolynomial (Fin n) R) :
    esymmSubst n p = (MvPolynomial.esymmAlgHom (Fin n) R n p).1 :=
  (MvPolynomial.esymmAlgHom_apply p).symm

/-- Substitution by the elementary symmetric polynomials is injective. -/
lemma esymmSubst_injective [CommRing R] (n : ℕ) :
    Function.Injective (esymmSubst (R := R) n) := fun p q hpq =>
  (MvPolynomial.esymmAlgHom_fin_bijective R n).1 <| Subtype.ext <| by
    simpa only [← esymmSubst_apply] using hpq

end esymmSubst

end TauCeti

namespace MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The universal resolvent has a unique expression in the elementary symmetric polynomials. -/
theorem existsUnique_orbitProduct (Φ : MvPolynomial (Fin n) R) :
    ∃! D : (MvPolynomial (Fin n) R)[X], D.map (TauCeti.esymmSubst n) = universalResolvent Φ := by
  obtain ⟨D, hD⟩ := (mem_lifts _).1 <| (lifts_iff_coeff_lifts _).2 fun k => by
    obtain ⟨p, hp⟩ := (esymmAlgHom_fin_bijective R n).2
      ⟨_, (mem_symmetricSubalgebra _).2 (isSymmetric_universalResolvent_coeff Φ k)⟩
    exact ⟨p, by rw [TauCeti.esymmSubst_apply, hp]⟩
  exact ⟨D, hD, fun E hE =>
    Polynomial.map_injective _ (TauCeti.esymmSubst_injective n) (hE.trans hD.symm)⟩

/-- An expression for the universal resolvent in the elementary symmetric polynomials is itself
monic, since elementary-symmetric substitution is injective. -/
theorem monic_of_map_esymmSubst_eq {Φ : MvPolynomial (Fin n) R}
    {D : (MvPolynomial (Fin n) R)[X]}
    (hD : D.map (TauCeti.esymmSubst n) = universalResolvent Φ) : D.Monic :=
  monic_of_injective (TauCeti.esymmSubst_injective n) (hD ▸ monic_universalResolvent Φ)

/-- An expression for the universal resolvent in the elementary symmetric polynomials has the
degree of the universal resolvent, the number of elements of the rename-orbit. -/
theorem natDegree_of_map_esymmSubst_eq [Nontrivial R] {Φ : MvPolynomial (Fin n) R}
    {D : (MvPolynomial (Fin n) R)[X]}
    (hD : D.map (TauCeti.esymmSubst n) = universalResolvent Φ) :
    D.natDegree = (renameOrbit Φ).card := by
  rw [← natDegree_map_eq_of_injective (TauCeti.esymmSubst_injective n) D, hD,
    natDegree_universalResolvent]

end MvPolynomial
