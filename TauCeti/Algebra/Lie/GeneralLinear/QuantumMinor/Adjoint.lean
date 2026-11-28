/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Row
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Tactic.Abel
import TauCeti.Algebra.Star.BigOperators

/-!
# Adjoints of quantum minors

If the adjoint transposes the generators with a sign at each of their indices, it transposes
quantum minors with the product of the corresponding row and column signs. In particular the
principal minors are self-adjoint at self-adjoint spectral parameters. The reversal of the
noncommutative products uses the row form, so the spectral shifts retain their order in the
resulting column formula.

The signed adjoint identity is `Formalism.FourierDecayAlt.Q.StarMinor` in L. Alpöge's
formalization of the Riemann hypothesis for Dirichlet L-functions.
-/

public section

open Equiv Equiv.Perm

namespace Matrix

variable {ι K A : Type*} [DecidableEq ι] [CommRing K] [StarRing K]
  [Ring A] [StarRing A] [Algebra K A] [StarModule K A]

-- The diagonal spectral shift transforms with the same signs as the generator: ε(i)² = 1.
private theorem star_quantumMinor_entry (E : Matrix ι ι A) (ε : ι → K)
    (hε : ∀ i, ε i ^ 2 = 1) (hE : ∀ i j, star (E i j) = (ε i * ε j) • E j i)
    (i j : ι) (t : K) :
    star ((if i = j then algebraMap K A t else 0) + E i j) =
      (ε j * ε i) • ((if j = i then algebraMap K A (star t) else 0) + E j i) := by
  by_cases h : i = j
  · subst j
    simp [hE, ← pow_two, hε, ← algebraMap_star_comm]
  · simp [h, Ne.symm h, hE, mul_comm]

/-- The adjoint exchanges the row and column tuples of a quantum minor and takes the adjoint
of its spectral parameter. Each occurrence of an index contributes its sign to the result. -/
theorem star_quantumMinor [HasUniqueDiv A] (E : Matrix ι ι A)
    (hE : E.HasMatrixUnitLieRelations) (ε : ι → K) (hε : ∀ i, ε i ^ 2 = 1)
    (hstar : ∀ i j, star (E i j) = (ε i * ε j) • E j i) {n : ℕ}
    (u : K) (a b : Fin n → ι) :
    star (E.quantumMinor u a b) =
      ((∏ i, ε (a i)) * (∏ i, ε (b i))) • E.quantumMinor (star u) b a := by
  -- Match the row expansion with the column expansion on the reversed tuples.
  let r : Perm (Fin n) := Fin.revPerm
  let f (σ : Perm (Fin n)) (i : Fin n) : A :=
    (if a i = b (σ i) then algebraMap K A (u - ((n - 1 : ℕ) : K) + i.val) else 0) +
      E (a i) (b (σ i))
  let g (σ : Perm (Fin n)) (i : Fin n) : A :=
    (if b (r (σ i)) = a (r i) then algebraMap K A (star u - (i.val : K)) else 0) +
      E (b (r (σ i))) (a (r i))
  have hr : r.symm = r := (rfl)
  have hshift (i : Fin n) : u - ((n - 1 : ℕ) : K) + (r i).val = u - (i.val : K) := by
    have hi : (r i).val + i.val = n - 1 := by
      simp only [r, Fin.revPerm_apply, Fin.val_rev]
      omega
    have hcast := congrArg (Nat.cast : ℕ → K) hi
    push_cast at hcast
    rw [← hcast]
    abel
  have hrev (σ : Perm (Fin n)) : ((List.ofFn (f σ)).map star).reverse =
      List.ofFn (fun i ↦ (ε (b (σ (r i))) * ε (a (r i))) • g (r.permCongr σ) i) := by
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    have hentry (j : Fin n) : star (f σ (r j)) =
        (ε (b (σ (r j))) * ε (a (r j))) • g (r.permCongr σ) j := by
      simp only [f, g, hshift, permCongr_apply, hr]
      simpa only [r, Fin.revPerm_apply, Fin.rev_rev, star_sub, star_natCast] using
        star_quantumMinor_entry E ε hε hstar (a (r j)) (b (σ (r j))) (u - j.val)
    simpa [List.getElem_reverse, r, Fin.rev, Nat.sub_sub, Nat.add_comm] using
      hentry ⟨i, by simpa using h₂⟩
  have hproduct (σ : Perm (Fin n)) : star (List.ofFn (f σ)).prod =
      ((∏ i, ε (a i)) * (∏ i, ε (b i))) • (List.ofFn (g (r.permCongr σ))).prod := by
    rw [TauCeti.star_list_prod, hrev]
    have h := (MultilinearMap.mkPiAlgebraFin K n A).map_smul_univ
      (fun i ↦ ε (b (σ (r i))) * ε (a (r i))) (g (r.permCongr σ))
    have hb := Equiv.prod_comp (σ * r) (ε ∘ b)
    have ha := Equiv.prod_comp r (ε ∘ a)
    simp only [Function.comp_apply, Perm.mul_apply] at ha hb
    simpa only [RingHom.id_apply, Finset.prod_mul_distrib, ha, hb, mul_comm,
      MultilinearMap.mkPiAlgebraFin_apply] using h
  have hminor : star (E.quantumMinor u a b) =
      ((∏ i, ε (a i)) * (∏ i, ε (b i))) • E.quantumMinor (star u) (b ∘ r) (a ∘ r) := by
    rw [E.quantumMinor_eq_columnDet_row hE, E.quantumMinor_eq_columnDet, columnDet_apply,
      columnDet_apply, star_sum, Finset.smul_sum]
    conv_rhs => rw [← Equiv.sum_comp r.permCongr]
    apply Finset.sum_congr rfl
    intro σ _
    simpa only [f, g, of_apply, Function.comp_apply, sign_permCongr, Units.smul_def,
      star_zsmul, smul_comm (sign σ : ℤ)] using congrArg ((sign σ : ℤ) • ·) (hproduct σ)
  -- The two tuple reversals contribute the same sign, so their signs cancel.
  have hrr : r * r = 1 := by ext i; simp [r]
  rw [hminor, E.quantumMinor_comp_perm_right hE, E.quantumMinor_comp_perm_left, smul_smul,
    ← sign_mul, hrr, sign_one, one_smul]

/-- A principal quantum minor is self-adjoint when its spectral parameter is self-adjoint. -/
theorem isSelfAdjoint_quantumMinor [HasUniqueDiv A] (E : Matrix ι ι A)
    (hE : E.HasMatrixUnitLieRelations) (ε : ι → K) (hε : ∀ i, ε i ^ 2 = 1)
    (hstar : ∀ i j, star (E i j) = (ε i * ε j) • E j i) {n : ℕ}
    {u : K} (hu : IsSelfAdjoint u) (a : Fin n → ι) :
    IsSelfAdjoint (E.quantumMinor u a a) := by
  rw [IsSelfAdjoint, E.star_quantumMinor hE ε hε hstar, hu.star_eq,
    ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun i _ ↦ by rw [← pow_two, hε]),
    Finset.prod_const_one, one_smul]

end Matrix
