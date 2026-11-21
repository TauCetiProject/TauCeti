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

Let `S` be a subalgebra of `A` and `I` a nilpotent ideal. If `S` maps onto `A/I` and contains
representatives spanning `I/I²`, then `S = A`. Thus algebra generators can be lifted from the
quotient and the first ideal layer; this is the step showing that lifts of vertex idempotents and
of a basis of the first radical layer generate a finite-dimensional basic algebra over an
algebraically closed field.

The intermediate power estimate records that products of these first-layer lifts span every
successive ideal layer. No commutativity of `A`, field hypothesis, or finite-dimensionality is
needed for the nilpotent-ideal criterion, and `I` need only be a left ideal.

`AlgHom.surjective_of_nilpotent_ideal` is the corresponding criterion for an algebra map:
surjectivity modulo `I` and spanning the first ideal layer imply surjectivity. For the radical
of an Artinian algebra, Mathlib's `IsArtinianRing.isNilpotent_jacobson` supplies nilpotence.

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
    (h : I.restrictScalars R ≤ S.toSubmodule ⊔ (I ^ 2).restrictScalars R)
    (n : ℕ) (hn : n ≠ 0) :
    (I ^ n).restrictScalars R ≤ S.toSubmodule ⊔ (I ^ (n + 1)).restrictScalars R := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [Submodule.restrictScalars_pow two_ne_zero] at h
  rw [Submodule.restrictScalars_pow m.succ_ne_zero,
    Submodule.restrictScalars_pow (m + 1).succ_ne_zero]
  set N := I.restrictScalars R
  set P := N ⊓ S.toSubmodule
  have hsq : N ^ 2 ≤ N := by
    rw [sq]
    exact Submodule.mul_le.mpr fun x _ y hy ↦ I.mul_mem_left x hy
  -- The chosen representatives can be taken inside the ideal, since the error lies in its square.
  have hNP : N ≤ P ⊔ N ^ 2 := fun x hx ↦ by
    obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp (h hx)
    exact Submodule.mem_sup.mpr
      ⟨b, Submodule.mem_inf.mpr ⟨(I.add_mem_iff_left (hsq hc)).mp hx, hb⟩, c, hc, rfl⟩
  have hP (m : ℕ) : P ^ m ≤ S.toSubmodule := by
    induction m with
    | zero => exact Submodule.one_le.mpr S.one_mem
    | succ m ih =>
      rw [pow_succ]
      exact Submodule.mul_le.mpr fun x hx y hy ↦ S.mul_mem (ih hx) hy.2
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
          exact (mul_le_mul_left (pow_le_pow_left' inf_le_left (m + 1)) _).trans
            (by rw [← pow_add]; exact le_sup_right)
  exact (hlayer m).trans (sup_le_sup_right (hP _) _)

/-- If a subalgebra maps onto the quotient by an ideal and contains representatives of its
first ideal layer, it maps onto the quotient by every power of that ideal. -/
theorem toSubmodule_sup_restrictScalars_pow_eq_top (S : Subalgebra R A) (I : Ideal A)
    (hquot : S.toSubmodule ⊔ I.restrictScalars R = ⊤)
    (hlayer : I.restrictScalars R ≤ S.toSubmodule ⊔ (I ^ 2).restrictScalars R)
    (n : ℕ) : S.toSubmodule ⊔ (I ^ n).restrictScalars R = ⊤ := by
  induction n with
  | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    obtain rfl | hn := eq_or_ne n 0
    · simpa only [Nat.zero_add, Submodule.pow_one] using hquot
    · exact top_unique (ih ▸ sup_le le_sup_left (S.pow_le_toSubmodule_sup_pow_succ I hlayer n hn))

/-- A subalgebra is the whole algebra if it maps onto the quotient by a nilpotent ideal and
contains representatives spanning the first ideal layer. -/
theorem eq_top_of_nilpotent_ideal (S : Subalgebra R A) (I : Ideal A)
    (hI : IsNilpotent I) (hquot : S.toSubmodule ⊔ I.restrictScalars R = ⊤)
    (hlayer : I.restrictScalars R ≤ S.toSubmodule ⊔ (I ^ 2).restrictScalars R) : S = ⊤ := by
  obtain ⟨n, hn⟩ := hI
  simpa [hn] using S.toSubmodule_sup_restrictScalars_pow_eq_top I hquot hlayer n

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
