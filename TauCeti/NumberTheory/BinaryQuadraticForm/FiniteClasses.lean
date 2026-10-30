/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.LagrangeReduction
public import TauCeti.NumberTheory.BinaryQuadraticForm.Split.Classes

/-!
# Finitely many classes of binary quadratic forms of each nonzero discriminant

For every nonzero integer `D` there is a finite set of integral binary quadratic forms that meets
every `SL(2, ℤ)`-class of forms of discriminant `D`
(`TauCeti.BinaryQuadraticForm.exists_finset_forall_exists_smul_mem`), so the forms of
discriminant `D` fall into finitely many classes
(`TauCeti.BinaryQuadraticForm.finite_orbitRel_quotient_of_forall_discrim_eq`). The forms need not be
primitive and no definiteness is assumed, so this covers positive definite, negative definite and
indefinite forms, of square and of nonsquare discriminant.

* For nonsquare `D` the Lagrange reduced forms of discriminant `D` meet every class
  (`TauCeti.BinaryQuadraticForm.exists_smul_mem_lagrangeReducedForms`).
* For a square `D = s²` the triangular forms `s x y + c y²` with `0 ≤ c < |s|` meet every class
  (`TauCeti.BinaryQuadraticForm.exists_smul_eq_splitTriangularForm_of_discrim_eq_sq`).

This is the form-side finiteness behind the finiteness of the class number of a nondegenerate
binary lattice, whose norm form has discriminant `-4 det L`.

## References

* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 13, for binary forms of arbitrary
  discriminant.
* D. A. Cox, *Primes of the Form x² + ny²*, §2, for Lagrange's reduction.
-/

public section

open MulAction
open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

/-- **Finitely many forms represent every class of a nonzero discriminant.** For `D ≠ 0` there is
a finite set `S` of integral binary quadratic forms such that every form of discriminant `D` is
properly equivalent to a member of `S`. For nonsquare `D` the Lagrange reduced forms serve; for
square `D = s²` the triangular forms `s x y + c y²` with `0 ≤ c < |s|` do. -/
theorem exists_finset_forall_exists_smul_mem {D : ℤ} (hD : D ≠ 0) :
    ∃ S : Finset (BinaryQuadraticForm ℤ), ∀ f : BinaryQuadraticForm ℤ, f.discrim = D →
      ∃ γ : SL(2, ℤ), γ • f ∈ S := by
  by_cases hsq : IsSquare D
  · obtain ⟨s, rfl⟩ := hsq
    have hs : s ≠ 0 := by rintro rfl; simp at hD
    refine ⟨(Finset.Ico 0 |s|).image (splitTriangularForm s), fun f hf ↦ ?_⟩
    obtain ⟨γ, c, hc₀, hcs, hγ⟩ :=
      exists_smul_eq_splitTriangularForm_of_discrim_eq_sq f hs (hf.trans (sq s).symm)
    exact ⟨γ, Finset.mem_image.mpr ⟨c, Finset.mem_Ico.mpr ⟨hc₀, hcs⟩, hγ.symm⟩⟩
  · refine ⟨lagrangeReducedForms D, fun f hf ↦ ?_⟩
    subst hf
    exact exists_smul_mem_lagrangeReducedForms f hsq

/-- **Finiteness of classes of a nonzero discriminant**: a set of integral binary quadratic forms
of one nonzero discriminant `D`, stable under `SL(2, ℤ)`, falls into finitely many
`SL(2, ℤ)`-classes. -/
theorem finite_orbitRel_quotient_of_forall_discrim_eq {D : ℤ} (hD : D ≠ 0)
    (s : SubMulAction SL(2, ℤ) (BinaryQuadraticForm ℤ)) (hs : ∀ f ∈ s, f.discrim = D) :
    Finite (orbitRel.Quotient SL(2, ℤ) s) := by
  obtain ⟨S, hS⟩ := exists_finset_forall_exists_smul_mem hD
  -- the members of `s` in `S` form a finite set meeting every class
  let R := {f : s // f.1 ∈ S}
  have : Finite R :=
    .of_injective (fun f : R ↦ (⟨f.1.1, f.2⟩ : S)) fun f g h ↦ by
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val h
  refine .of_surjective (fun f : R ↦ (Quotient.mk'' f.1 : orbitRel.Quotient SL(2, ℤ) s))
    (Quotient.ind' fun f ↦ ?_)
  obtain ⟨γ, hγ⟩ := hS f.1 (hs f.1 f.2)
  exact ⟨⟨γ • f, hγ⟩, Quotient.sound' ⟨γ, rfl⟩⟩

/-- There are finitely many proper equivalence classes of primitive integral binary quadratic
forms of a nonzero discriminant `D`, square or not, positive or negative. -/
instance finite_orbitRel_quotient_primitiveForms {D : ℤ} [NeZero D] :
    Finite (orbitRel.Quotient SL(2, ℤ) (primitiveForms D)) :=
  finite_orbitRel_quotient_of_forall_discrim_eq (NeZero.ne D) _ fun f hf ↦
    ((mem_primitiveForms D f).1 hf).1

end TauCeti.BinaryQuadraticForm
