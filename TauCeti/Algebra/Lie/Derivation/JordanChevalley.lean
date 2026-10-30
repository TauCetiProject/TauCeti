/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.JordanChevalley
public import TauCeti.LinearAlgebra.Eigenspace.Minpoly

/-!
# Jordan–Chevalley decomposition of Lie derivations

The Jordan–Chevalley decomposition `D = N + S` of a derivation `D` of a finite-dimensional Lie
algebra, taken in the associative algebra of endomorphisms, has both parts again derivations.
This is not formal: the parts are polynomials in `D`, and a polynomial expression in a
derivation is in general not a derivation. The proof goes through generalized eigenspaces.

* A twisted Leibniz rule shows that the bracket of a generalized `a`-eigenvector and a
  generalized `b`-eigenvector of a derivation is a generalized `(a + b)`-eigenvector.
* The semisimple part `S` acts by the scalar `a` on the generalized `a`-eigenspace of `D`.
  Hence `S` satisfies the Leibniz rule on pairs of generalized eigenvectors, and so everywhere
  once the generalized eigenspaces of `D` span, for instance over an algebraically closed field.
  The nilpotent part `N = D - S` is then a derivation by subtraction.

The second step adapts the argument in Mathlib's proof of
`LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra`, which shows the same way that
the semisimple part of `ad x` is a derivation, with root spaces of a Cartan subalgebra in place of
the generalized eigenspaces of `D`.

This is the derivation-level input for the abstract Jordan decomposition of elements of a Lie
algebra all of whose derivations are inner.

## Main results

* `LieDerivation.pow_sub_smul_one_apply_lie`: the twisted Leibniz rule for powers of `D - c`.
* `LieDerivation.lie_mem_maxGenEigenspace`: brackets of generalized eigenvectors of a
  derivation add their eigenvalues.
* `LieDerivation.apply_lie_eq_add_of_isNilpotent_sub`: an endomorphism commuting with a split
  derivation `D`, finitely semisimple, and differing from `D` by a nilpotent map, satisfies the
  Leibniz rule.
* `LieDerivation.exists_isNilpotent_isSemisimple_of_iSup_maxGenEigenspace_eq_top` and
  `LieDerivation.exists_isNilpotent_isSemisimple`: the nilpotent and semisimple parts of a split
  derivation, respectively of any derivation over an algebraically closed field, are
  derivations.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §4.2,
  Lemma 4.2 (the semisimple and nilpotent parts of a derivation are derivations).
-/

public section

open Finset Module.End

namespace LieDerivation

section CommRing

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The twisted Leibniz rule: for a derivation `D` and scalars `a`, `b`, powers of `D - (a + b)`
applied to a bracket expand binomially into powers of `D - a` and `D - b` applied to the two
arguments. For `a = b = 0` this is `LieDerivation.iterate_apply_lie`. -/
theorem pow_sub_smul_one_apply_lie (D : LieDerivation R L L) (a b : R) (n : ℕ) (x y : L) :
    (((D : Module.End R L) - (a + b) • 1) ^ n) ⁅x, y⁆ =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 •
        ⁅(((D : Module.End R L) - a • 1) ^ ij.1) x, (((D : Module.End R L) - b • 1) ^ ij.2) y⁆ := by
  set A := (D : Module.End R L) - a • 1
  set B := (D : Module.End R L) - b • 1
  have key (u v : L) :
      ((D : Module.End R L) - (a + b) • 1) ⁅u, v⁆ = ⁅A u, v⁆ + ⁅u, B v⁆ := by
    simp only [A, B, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      LieDerivation.coeFn_coe, apply_lie_eq_add, sub_lie, lie_sub, smul_lie, lie_smul, add_smul,
      LinearMap.add_apply]
    abel
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul (M := L) (fun i j => ⁅(A ^ i) x, (B ^ j) y⁆) n,
      pow_succ', Module.End.mul_apply, ih]
    simp only [map_sum, map_nsmul, key, smul_add, sum_add_distrib, pow_succ', Module.End.mul_apply]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun ⟨i, j⟩ hij ↦ ?_
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]

/-- The bracket of a generalized `a`-eigenvector and a generalized `b`-eigenvector of a
derivation is a generalized `(a + b)`-eigenvector. -/
theorem lie_mem_maxGenEigenspace (D : LieDerivation R L L) {a b : R} {x y : L}
    (hx : x ∈ maxGenEigenspace (D : Module.End R L) a)
    (hy : y ∈ maxGenEigenspace (D : Module.End R L) b) :
    ⁅x, y⁆ ∈ maxGenEigenspace (D : Module.End R L) (a + b) := by
  rw [Module.End.mem_maxGenEigenspace] at hx hy ⊢
  obtain ⟨k, hk⟩ := hx
  obtain ⟨l, hl⟩ := hy
  refine ⟨k + l - 1, ?_⟩
  rw [pow_sub_smul_one_apply_lie]
  refine sum_eq_zero fun ⟨i, j⟩ hij ↦ ?_
  rcases Nat.le_or_le_of_add_eq_add_pred (mem_antidiagonal.mp hij) with hi | hj
  · rw [Module.End.pow_map_zero_of_le hi hk, zero_lie, smul_zero]
  · rw [Module.End.pow_map_zero_of_le hj hl, lie_zero, smul_zero]

end CommRing

section Field

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- Let `D` be a derivation whose generalized eigenspaces span. An endomorphism `S` commuting
with `D`, finitely semisimple, and such that `D - S` is nilpotent, satisfies the Leibniz rule.
Over a perfect field and in finite dimension, such an `S` is exactly the semisimple part of
`D`, by uniqueness of the Jordan–Chevalley decomposition. -/
theorem apply_lie_eq_add_of_isNilpotent_sub (D : LieDerivation K L L)
    (hD : ⨆ μ, maxGenEigenspace (D : Module.End K L) μ = ⊤) {S : Module.End K L}
    (hDS : Commute (D : Module.End K L) S) (hS : S.IsFinitelySemisimple)
    (hN : IsNilpotent ((D : Module.End K L) - S)) (x y : L) :
    S ⁅x, y⁆ = ⁅x, S y⁆ + ⁅S x, y⁆ := by
  have hev {μ : K} {z : L} (hz : z ∈ maxGenEigenspace (D : Module.End K L) μ) : S z = μ • z :=
    apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hz hDS hS hN
  have hx : x ∈ ⨆ μ, maxGenEigenspace (D : Module.End K L) μ := hD ▸ Submodule.mem_top
  have hy : y ∈ ⨆ μ, maxGenEigenspace (D : Module.End K L) μ := hD ▸ Submodule.mem_top
  induction hx using Submodule.iSup_induction' with
  | mem a x hx =>
    induction hy using Submodule.iSup_induction' with
    | mem b y hy =>
      rw [hev hx, hev hy, hev (D.lie_mem_maxGenEigenspace hx hy), smul_lie, lie_smul, add_comm,
        add_smul]
    | zero => simp
    | add _ _ _ _ h h' => simp only [lie_add, map_add, h, h']; abel
  | zero => simp
  | add _ _ _ _ h h' => simp only [add_lie, map_add, h, h']; abel

variable [FiniteDimensional K L]

open Polynomial in
/-- **Jordan–Chevalley decomposition of a split derivation.** If the generalized eigenspaces of
a derivation `D` of a finite-dimensional Lie algebra span, then the nilpotent and semisimple parts
of `D` are derivations. They are polynomials in `D`. No perfectness of the field is needed: `D`
is annihilated by a power of the separable polynomial whose simple roots are its eigenvalues. -/
theorem exists_isNilpotent_isSemisimple_of_iSup_maxGenEigenspace_eq_top (D : LieDerivation K L L)
    (hD : ⨆ μ, maxGenEigenspace (D : Module.End K L) μ = ⊤) :
    ∃ N S : LieDerivation K L L,
      (N : Module.End K L) ∈ Algebra.adjoin K {(D : Module.End K L)} ∧
      (S : Module.End K L) ∈ Algebra.adjoin K {(D : Module.End K L)} ∧
      IsNilpotent (N : Module.End K L) ∧ IsSemisimple (S : Module.End K L) ∧ D = N + S := by
  classical
  set T := (finite_hasEigenvalue (D : Module.End K L)).toFinset
  have hsep : (∏ μ ∈ T, (X - C μ)).Separable :=
    separable_prod_X_sub_C_iff'.mpr fun _ _ _ _ ↦ id
  have hdvd : minpoly K (D : Module.End K L) ∣ (∏ μ ∈ T, (X - C μ)) ^ Module.finrank K L :=
    minpoly_dvd_prod_X_sub_C_pow_of_iSup_maxGenEigenspace_eq_top hD
  obtain ⟨n, hn, s, hs, hn_nil, hs_ss, hDns⟩ :=
    exists_isNilpotent_isSemisimple_of_separable_of_dvd_pow hsep hdvd
  have hDs : Commute (D : Module.End K L) s := Algebra.commute_of_mem_adjoin_self hs
  have hsub : (D : Module.End K L) - s = n := by rw [hDns, add_sub_cancel_right]
  have hleib := D.apply_lie_eq_add_of_isNilpotent_sub hD hDs hs_ss.isFinitelySemisimple
    (hsub ▸ hn_nil)
  let S : LieDerivation K L L :=
    { toLinearMap := s
      leibniz' := fun x y ↦ by rw [hleib, ← lie_skew y, sub_neg_eq_add] }
  have hDS : ((D - S : LieDerivation K L L) : Module.End K L) = n := by
    rw [coe_sub_linearMap]
    exact hsub
  exact ⟨D - S, S, hDS ▸ hn, hs, hDS ▸ hn_nil, hs_ss, (sub_add_cancel D S).symm⟩

/-- **Jordan–Chevalley decomposition of a derivation.** Over an algebraically closed field, the
nilpotent and semisimple parts of a derivation of a finite-dimensional Lie algebra are
derivations. They are polynomials in the original derivation. -/
theorem exists_isNilpotent_isSemisimple [IsAlgClosed K] (D : LieDerivation K L L) :
    ∃ N S : LieDerivation K L L,
      (N : Module.End K L) ∈ Algebra.adjoin K {(D : Module.End K L)} ∧
      (S : Module.End K L) ∈ Algebra.adjoin K {(D : Module.End K L)} ∧
      IsNilpotent (N : Module.End K L) ∧ IsSemisimple (S : Module.End K L) ∧ D = N + S :=
  D.exists_isNilpotent_isSemisimple_of_iSup_maxGenEigenspace_eq_top
    (iSup_maxGenEigenspace_eq_top _)

end Field

end LieDerivation
