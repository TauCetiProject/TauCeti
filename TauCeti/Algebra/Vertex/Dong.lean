/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import TauCeti.Algebra.Vertex.ResidueProduct
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# Dong's lemma for nonnegative residue products

If three fields `A(z)`, `B(z)` and `C(z)` are pairwise mutually local, then every nonnegative
residue product `A₍ₙ₎B = Res_z (z - w)ⁿ [A(z), B(w)]` is again local with `C(z)`
(`VertexOperator.IsLocalOfOrder.nonnegResidueProduct`). Explicitly, if the three pairs are local
of orders `N_AB`, `N_AC` and `N_BC`, then `A₍ₙ₎B` and `C` are local of order
`N_AB + N_AC + N_BC`, for every `n`.

The proof works with the three-variable distribution `[[A(x), B(w)], C(z)]`, read
coefficientwise, on which multiplication by `x - w`, `x - z` and `w - z` are commuting
operators. By the Jacobi identity it is the sum of `[A(x), [B(w), C(z)]]`, killed by
`(w - z)^N_BC`, and `[[A(x), C(z)], B(w)]`, killed by `(x - z)^N_AC`, while the whole
distribution is killed by `(x - w)^N_AB`. Writing `w - z = (x - z) - (x - w)` and expanding,
every term of `(w - z)^(N_AB + N_AC + N_BC)` falls under one of these three annihilators.
Taking the residue against `(x - w)ⁿ` commutes with multiplication by `w - z`.

In a formal vertex algebra all fields are pairwise local, so every nonnegative residue product
of two fields `Y(a,z)` and `Y(b,z)` is local with every field `Y(c,z)`
(`TauCeti.FormalVertexAxioms.exists_isLocalOfOrder_nonnegResidueProduct`). This is the locality
hypothesis of Goddard's uniqueness theorem for these products, as used for the commutator
formula and the reconstruction of vertex algebras from generating fields.

## Main results

* `VertexOperator.IsLocalOfOrder.nonnegResidueProduct`: Dong's lemma for nonnegative residue
  products.
* `TauCeti.FormalVertexAxioms.exists_isLocalOfOrder_nonnegResidueProduct`: in a formal vertex
  algebra, `Y(a,z)₍ₙ₎Y(b,z)` is local with every `Y(c,z)`.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., Chapter 3, Dong's lemma, whose proof by
  expanding `w - z = (x - z) - (x - w)` is followed here.
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), where the lemma is attributed to C. Dong.
-/

public section

noncomputable section

open Finset
open scoped VertexOperator

namespace VertexOperator

/-! ### Multiplication of three-variable distributions by the variables -/

section Shift

variable {M : Type*} [AddCommGroup M]

/-- `ℤ`-linear endomorphisms of three-variable distributions `ℤ → ℤ → ℤ → M`, among which are the
multiplications by the three variables. -/
private abbrev Op (M : Type*) [AddCommGroup M] := Module.End ℤ (ℤ → ℤ → ℤ → M)

/-- Multiplication of a three-variable distribution `d a b c`, the coefficient of
`x^(-a-1) w^(-b-1) z^(-c-1)`, by the first variable `x`. -/
private def shift₁ : Op M where
  toFun d a b c := d (a + 1) b c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication of a three-variable distribution by the second variable `w`. -/
private def shift₂ : Op M where
  toFun d a b c := d a (b + 1) c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication of a three-variable distribution by the third variable `z`. -/
private def shift₃ : Op M where
  toFun d a b c := d a b (c + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem shift₁_apply (d : ℤ → ℤ → ℤ → M) (a b c : ℤ) :
    shift₁ (M := M) d a b c = d (a + 1) b c :=
  rfl

private theorem shift₂_apply (d : ℤ → ℤ → ℤ → M) (a b c : ℤ) :
    shift₂ (M := M) d a b c = d a (b + 1) c :=
  rfl

private theorem shift₃_apply (d : ℤ → ℤ → ℤ → M) (a b c : ℤ) :
    shift₃ (M := M) d a b c = d a b (c + 1) :=
  rfl

private theorem commute_shift₁_shift₂ : Commute (shift₁ (M := M)) shift₂ :=
  LinearMap.ext fun _ ↦ rfl

private theorem commute_shift₁_shift₃ : Commute (shift₁ (M := M)) shift₃ :=
  LinearMap.ext fun _ ↦ rfl

private theorem commute_shift₂_shift₃ : Commute (shift₂ (M := M)) shift₃ :=
  LinearMap.ext fun _ ↦ rfl

private theorem shift₁_pow_apply (k : ℕ) (d : ℤ → ℤ → ℤ → M) (a b c : ℤ) :
    (shift₁ (M := M) ^ k) d a b c = d (a + k) b c := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, shift₁_apply, ih]
    congr 1
    push_cast
    ring

private theorem shift₂_pow_apply (k : ℕ) (d : ℤ → ℤ → ℤ → M) (a b c : ℤ) :
    (shift₂ (M := M) ^ k) d a b c = d a (b + k) c := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, shift₂_apply, ih]
    congr 1
    push_cast
    ring

private theorem shift₃_pow_apply (k : ℕ) (d : ℤ → ℤ → ℤ → M) (a b c : ℤ) :
    (shift₃ (M := M) ^ k) d a b c = d a b (c + k) := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, shift₃_apply, ih]
    congr 1
    push_cast
    ring

/-- The binomial expansion of `(u - v)ᴺ` for commuting operators. -/
private theorem sub_pow_apply {u v : Op M} (h : Commute u v) (N : ℕ)
    (d : ℤ → ℤ → ℤ → M) :
    ((u - v) ^ N) d =
      ∑ ij ∈ antidiagonal N, N.choose ij.1 • (-1 : ℤ) ^ ij.2 • (u ^ ij.1) ((v ^ ij.2) d) := by
  rw [sub_eq_add_neg, ← neg_one_zsmul, (h.smul_right (-1 : ℤ)).add_pow' N, LinearMap.sum_apply]
  refine sum_congr rfl fun ij _ ↦ ?_
  rw [smul_pow, mul_smul_comm, LinearMap.smul_apply, LinearMap.smul_apply, mul_apply_eq_comp]

/-- The combinatorial core of Dong's lemma. Let `d = d₁ + d₂` be three-variable distributions in
`x, w, z` such that `(x - w)^N_AB` kills `d`, `(x - z)^N_AC` kills `d₂` and `(w - z)^N_BC` kills
`d₁`. Then `(w - z)^(N_AB + N_AC + N_BC)` kills `d`. -/
private theorem sub_pow_eq_zero {d d₁ d₂ : ℤ → ℤ → ℤ → M} (hd : d = d₁ + d₂) {Nab Nac Nbc : ℕ}
    (hab : ((shift₁ - shift₂ : Op M) ^ Nab) d = 0)
    (hac : ((shift₁ - shift₃ : Op M) ^ Nac) d₂ = 0)
    (hbc : ((shift₂ - shift₃ : Op M) ^ Nbc) d₁ = 0) :
    ((shift₂ - shift₃ : Op M) ^ (Nab + Nac + Nbc)) d = 0 := by
  have c₁₂ := commute_shift₁_shift₂ (M := M)
  have c₁₃ := commute_shift₁_shift₃ (M := M)
  have c₂₃ := commute_shift₂_shift₃ (M := M)
  -- Write `w - z = u + v` with `u = x - z` and `v = w - x = -(x - w)`.
  set u : Op M := shift₁ - shift₃ with hu
  set v : Op M := shift₂ - shift₁ with hv
  have huv : Commute u v :=
    (c₁₂.sub_right (Commute.refl _)).sub_left (c₂₃.symm.sub_right c₁₃.symm)
  have hwu : Commute (shift₂ - shift₃) u :=
    (c₁₂.symm.sub_right c₂₃).sub_left (c₁₃.symm.sub_right (Commute.refl _))
  have hwv : Commute (shift₂ - shift₃) v :=
    ((Commute.refl _).sub_right c₁₂.symm).sub_left (c₂₃.symm.sub_right c₁₃.symm)
  have hw : shift₂ - shift₃ = u + v := by rw [hu, hv]; abel
  have hvd : (v ^ Nab) d = 0 := by
    rw [hv, ← neg_sub, neg_pow, mul_apply_eq_comp, hab, map_zero]
  rw [show Nab + Nac + Nbc = Nbc + (Nab + Nac) by ring, pow_add, mul_apply_eq_comp]
  nth_rw 2 [hw]
  rw [huv.add_pow', LinearMap.sum_apply, map_sum]
  refine sum_eq_zero fun ij hij ↦ ?_
  rw [LinearMap.smul_apply, map_nsmul]
  rw [HasAntidiagonal.mem_antidiagonal] at hij
  by_cases hi : Nac ≤ ij.1
  · -- The term is killed on `d₁` by `(w - z)^N_BC`, and on `d₂` by `(x - z)^N_AC`.
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi
    have h₁ : ((shift₂ - shift₃ : Op M) ^ Nbc) ((u ^ ij.1 * v ^ ij.2) d₁) = 0 := by
      rw [← mul_apply_eq_comp, ((hwu.pow_pow _ _).mul_right (hwv.pow_pow _ _)).eq,
        mul_apply_eq_comp, hbc, map_zero]
    have h₂ : (u ^ ij.1 * v ^ ij.2) d₂ = 0 := by
      rw [hk, pow_add, mul_assoc, ((Commute.pow_pow_self u Nac k).mul_right
        (huv.pow_pow Nac ij.2)).eq, mul_apply_eq_comp, hac, map_zero]
    rw [hd, map_add, map_add, h₁, h₂, map_zero, add_zero, smul_zero]
  · -- The term is killed by `(x - w)^N_AB`.
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (show Nab ≤ ij.2 by omega)
    rw [hk, pow_add, ← mul_assoc, mul_apply_eq_comp, hvd, map_zero, map_zero, smul_zero]

end Shift

/-! ### Dong's lemma -/

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Dong's lemma** for nonnegative residue products: if `A`, `B` and `C` are pairwise mutually
local, of orders `N_AB`, `N_AC` and `N_BC`, then every residue product
`A₍ₙ₎B = Res_z (z - w)ⁿ [A(z), B(w)]` is local with `C`, of order `N_AB + N_AC + N_BC`. -/
theorem IsLocalOfOrder.nonnegResidueProduct {A B C : VertexOperator R V} {Nab Nac Nbc : ℕ}
    (hAB : A.IsLocalOfOrder B Nab) (hAC : A.IsLocalOfOrder C Nac)
    (hBC : B.IsLocalOfOrder C Nbc) (n : ℕ) :
    (nonnegResidueProduct n A B).IsLocalOfOrder C (Nab + Nac + Nbc) := by
  -- The coefficients of `[[A(x), B(w)], C(z)]` and of its two Jacobi summands.
  set d : ℤ → ℤ → ℤ → Module.End R V := fun a b c ↦
    (A[[a]] * B[[b]] - B[[b]] * A[[a]]) * C[[c]] - C[[c]] * (A[[a]] * B[[b]] - B[[b]] * A[[a]])
  set d₁ : ℤ → ℤ → ℤ → Module.End R V := fun a b c ↦
    A[[a]] * (B[[b]] * C[[c]] - C[[c]] * B[[b]]) - (B[[b]] * C[[c]] - C[[c]] * B[[b]]) * A[[a]]
  set d₂ : ℤ → ℤ → ℤ → Module.End R V := fun a b c ↦
    (A[[a]] * C[[c]] - C[[c]] * A[[a]]) * B[[b]] - B[[b]] * (A[[a]] * C[[c]] - C[[c]] * A[[a]])
  have hjac : d = d₁ + d₂ := by
    funext a b c
    simp only [d, d₁, d₂, Pi.add_apply]
    noncomm_ring
  have hab : ((shift₁ - shift₂ : Op (Module.End R V)) ^ Nab) d = 0 := by
    funext a b c
    simp only [sub_pow_apply commute_shift₁_shift₂, Finset.sum_apply, Pi.smul_apply,
      shift₁_pow_apply, shift₂_pow_apply, d, Pi.zero_apply]
    -- Take the commutator with `C[[c]]` of a locality relation between the other two fields.
    have h := congr_arg (AddMonoidHom.mulRight (C[[c]]) - AddMonoidHom.mulLeft (C[[c]]))
      (isLocalOfOrder_iff.mp hAB a b)
    simpa only [map_sum, map_nsmul, map_zsmul, map_zero, AddMonoidHom.sub_apply,
      AddMonoidHom.mulRight_apply, AddMonoidHom.coe_mulLeft] using h
  have hac : ((shift₁ - shift₃ : Op (Module.End R V)) ^ Nac) d₂ = 0 := by
    funext a b c
    simp only [sub_pow_apply commute_shift₁_shift₃, Finset.sum_apply, Pi.smul_apply,
      shift₁_pow_apply, shift₃_pow_apply, d₂, Pi.zero_apply]
    -- Take the commutator with `B[[b]]` of a locality relation between the other two fields.
    have h := congr_arg (AddMonoidHom.mulRight (B[[b]]) - AddMonoidHom.mulLeft (B[[b]]))
      (isLocalOfOrder_iff.mp hAC a c)
    simpa only [map_sum, map_nsmul, map_zsmul, map_zero, AddMonoidHom.sub_apply,
      AddMonoidHom.mulRight_apply, AddMonoidHom.coe_mulLeft] using h
  have hbc : ((shift₂ - shift₃ : Op (Module.End R V)) ^ Nbc) d₁ = 0 := by
    funext a b c
    simp only [sub_pow_apply commute_shift₂_shift₃, Finset.sum_apply, Pi.smul_apply,
      shift₂_pow_apply, shift₃_pow_apply, d₁, Pi.zero_apply]
    -- Take the commutator of `A[[a]]` with a locality relation between `B` and `C`.
    have h := congr_arg (AddMonoidHom.mulLeft (A[[a]]) - AddMonoidHom.mulRight (A[[a]]))
      (isLocalOfOrder_iff.mp hBC b c)
    simpa only [map_sum, map_nsmul, map_zsmul, map_zero, AddMonoidHom.sub_apply,
      AddMonoidHom.mulRight_apply, AddMonoidHom.coe_mulLeft] using h
  have key := sub_pow_eq_zero hjac hab hac hbc
  -- Expand the residue product and exchange the two binomial sums; each inner sum is a
  -- coefficient of `(w - z)^(N_AB + N_AC + N_BC) [[A(x), B(w)], C(z)] = 0`.
  rw [isLocalOfOrder_iff]
  intro p q
  simp only [ncoeff_nonnegResidueProduct, sum_mul, mul_sum, ← sum_sub_distrib, smul_mul_assoc,
    mul_smul_comm, ← smul_sub, smul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun kl _ ↦ ?_
  have hk := congr_fun (congr_fun (congr_fun key kl.1) (p + kl.2)) q
  simp only [sub_pow_apply commute_shift₂_shift₃, Finset.sum_apply, Pi.smul_apply,
    shift₂_pow_apply, shift₃_pow_apply, d, Pi.zero_apply] at hk
  rw [← smul_zero (n.choose kl.1), ← smul_zero ((-1 : ℤ) ^ kl.2), ← hk, smul_sum, smul_sum]
  refine sum_congr rfl fun ij _ ↦ ?_
  rw [show p + ij.1 + kl.2 = p + kl.2 + ij.1 by ring]
  module

end VertexOperator

namespace TauCeti.FormalVertexAxioms

open VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- In a formal vertex algebra, every nonnegative residue product `Y(a,z)₍ₙ₎Y(b,z)` of two fields
is local with every field `Y(c,z)`. -/
theorem exists_isLocalOfOrder_nonnegResidueProduct (A : FormalVertexAxioms R V) (n : ℕ)
    (a b c : V) :
    ∃ N, (nonnegResidueProduct n (A.field a) (A.field b)).IsLocalOfOrder (A.field c) N := by
  obtain ⟨_, hab⟩ := A.exists_isLocalOfOrder a b
  obtain ⟨_, hac⟩ := A.exists_isLocalOfOrder a c
  obtain ⟨_, hbc⟩ := A.exists_isLocalOfOrder b c
  exact ⟨_, hab.nonnegResidueProduct hac hbc n⟩

end TauCeti.FormalVertexAxioms
