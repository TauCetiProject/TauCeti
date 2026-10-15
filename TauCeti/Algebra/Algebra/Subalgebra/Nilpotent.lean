/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Generating an algebra modulo a nilpotent ideal

Let `S` be a subalgebra of `A` and `I` a nilpotent two-sided ideal. If `S` maps onto `A/I`
and contains representatives spanning `I/I²`, then `S = A`. Thus algebra generators can be
lifted from the quotient and the first ideal layer. In particular, lifts of vertex idempotents
and of a basis of the first radical layer generate a finite-dimensional basic algebra over an
algebraically closed field.

The intermediate power estimate records that products of these first-layer lifts span every
successive ideal layer. No commutativity of `A`, field hypothesis, or finite-dimensionality is
needed for the nilpotent-ideal criterion.

`AlgHom.surjective_of_nilpotent_ideal` is the corresponding criterion for an algebra map:
surjectivity modulo `I` and spanning the first ideal layer imply surjectivity. For the radical
of an Artinian algebra, Mathlib's `IsArtinianRing.isNilpotent_jacobson_bot` supplies nilpotence.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter II, §3 (the generation step in the bound-quiver presentation).
-/

public section

namespace Subalgebra

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- If a subalgebra contains representatives of the first ideal layer, it contains
representatives of every positive ideal layer. -/
theorem pow_le_toSubmodule_sup_pow_succ (S : Subalgebra R A) (I : Ideal A)
    [I.IsTwoSided]
    (h : I.restrictScalars R ≤ S.toSubmodule ⊔ (I ^ 2).restrictScalars R)
    (n : ℕ) (hn : n ≠ 0) :
    (I ^ n).restrictScalars R ≤ S.toSubmodule ⊔ (I ^ (n + 1)).restrictScalars R := by
  let N := I.restrictScalars R
  let P := S.toSubmodule ⊓ N
  -- The chosen representatives lie in the ideal, since the error lies in its square.
  have hNP : N ≤ P ⊔ N ^ 2 := by
    intro x hx
    obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp (h hx)
    have hbI : b ∈ I := by
      have hb' : b = x - c := by rw [← hbc]; abel
      rw [hb']
      have hcI : c ∈ I ^ 2 := (Submodule.restrictScalars_mem R (I ^ 2) c).mp hc
      rw [Submodule.pow_succ, Submodule.pow_one] at hcI
      exact I.sub_mem hx (Ideal.mul_le_left hcI)
    exact Submodule.mem_sup.mpr ⟨b, ⟨hb, hbI⟩, c,
      by simpa only [N, Submodule.restrictScalars_pow (by decide : 2 ≠ 0)] using hc, hbc⟩
  have hP (m : ℕ) : P ^ m ≤ S.toSubmodule := by
    induction m with
    | zero => exact Submodule.one_le.mpr S.one_mem
    | succ m ih =>
      rw [pow_succ]
      exact Submodule.mul_le.mpr fun x hx y hy ↦ S.mul_mem (ih hx) hy.1
  -- Replace one factor at a time; every error belongs to the next ideal power.
  have hlayer : ∀ m : ℕ, N ^ (m + 1) ≤ P ^ (m + 1) ⊔ N ^ (m + 2) := by
    intro m
    induction m with
    | zero => simpa only [Nat.zero_add, pow_one] using hNP
    | succ m ih =>
      calc
        N ^ (m + 1 + 1) ≤ (P ^ (m + 1) ⊔ N ^ (m + 2)) * N := by
          rw [pow_succ]
          exact mul_le_mul_left ih N
        _ = P ^ (m + 1) * N ⊔ N ^ (m + 3) := by
          rw [Submodule.sup_mul, ← pow_succ]
        _ ≤ P ^ (m + 1) * (P ⊔ N ^ 2) ⊔ N ^ (m + 3) :=
          sup_le_sup (mul_le_mul_right hNP _) le_rfl
        _ = P ^ (m + 2) ⊔ P ^ (m + 1) * N ^ 2 ⊔ N ^ (m + 3) := by
          rw [Submodule.mul_sup, ← pow_succ]
        _ ≤ P ^ (m + 2) ⊔ N ^ (m + 3) := by
          refine sup_le (sup_le le_sup_left ?_) le_sup_right
          exact (mul_le_mul_left (pow_le_pow_left' inf_le_right (m + 1)) _).trans
            (by rw [← pow_add]; exact le_sup_right)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simpa only [N, Submodule.restrictScalars_pow (Nat.succ_ne_zero _)] using
    (hlayer m).trans (sup_le_sup (hP (m + 1)) le_rfl)

/-- If a subalgebra maps onto the quotient by an ideal and contains representatives of its
first ideal layer, it maps onto the quotient by every power of that ideal. -/
theorem toSubmodule_sup_pow_restrictScalars_eq_top_of_le_sup_sq
    (S : Subalgebra R A) (I : Ideal A) [I.IsTwoSided]
    (hquot : S.toSubmodule ⊔ I.restrictScalars R = ⊤)
    (hlayer : I.restrictScalars R ≤ S.toSubmodule ⊔ (I ^ 2).restrictScalars R)
    (n : ℕ) : S.toSubmodule ⊔ (I ^ n).restrictScalars R = ⊤ := by
  cases n with
  | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
  | succ n =>
    induction n with
    | zero => simpa only [Nat.zero_add, Submodule.pow_one] using hquot
    | succ n ih =>
      apply top_unique
      rw [← ih]
      exact sup_le le_sup_left (S.pow_le_toSubmodule_sup_pow_succ I hlayer _
        (Nat.succ_ne_zero _))

/-- A subalgebra is the whole algebra if it maps onto the quotient by a nilpotent two-sided
ideal and contains representatives spanning the first ideal layer. -/
theorem eq_top_of_nilpotent_ideal (S : Subalgebra R A) (I : Ideal A) [I.IsTwoSided]
    (hI : IsNilpotent I) (hquot : S.toSubmodule ⊔ I.restrictScalars R = ⊤)
    (hlayer : I.restrictScalars R ≤ S.toSubmodule ⊔ (I ^ 2).restrictScalars R) : S = ⊤ := by
  obtain ⟨n, hn⟩ := hI
  have h := S.toSubmodule_sup_pow_restrictScalars_eq_top_of_le_sup_sq I hquot hlayer n
  simpa [hn] using h

end Subalgebra

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Ring B]
  [Algebra R A] [Algebra R B]

/-- An algebra map is surjective if it is surjective modulo a nilpotent two-sided ideal and
its range contains representatives spanning the first ideal layer. -/
theorem surjective_of_nilpotent_ideal (f : A →ₐ[R] B) (I : Ideal B) [I.IsTwoSided]
    (hI : IsNilpotent I)
    (hquot : Function.Surjective ((Ideal.Quotient.mkₐ R I).comp f))
    (hlayer : I.restrictScalars R ≤ f.range.toSubmodule ⊔ (I ^ 2).restrictScalars R) :
    Function.Surjective f := by
  apply f.range_eq_top.mp
  apply f.range.eq_top_of_nilpotent_ideal I hI ?_ hlayer
  apply top_unique
  intro x _
  obtain ⟨a, ha⟩ := hquot (Ideal.Quotient.mkₐ R I x)
  have hxa : Ideal.Quotient.mk I x = Ideal.Quotient.mk I (f a) := by
    simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using ha.symm
  exact Submodule.mem_sup.mpr ⟨f a, f.mem_range_self a, x - f a,
    (Submodule.restrictScalars_mem R I _).mpr (Ideal.Quotient.eq.mp hxa), by abel⟩

end AlgHom
