/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.BinaryForm.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Comap

/-!
# Frobenius submodules of binary forms

In characteristic `p`, the homogeneous polynomials in `x^p` and `y^p` form a rational
`SL₂`-subrepresentation of the binary forms of degree `p * m`. In positive degree this
subrepresentation is nonzero and proper: it contains `y^(p*m)` but misses
`x * y^(p*m-1)`. Thus binary forms of positive degree divisible by the characteristic
are not simple, over every field, including imperfect and finite fields.

The construction uses `Comodule.polynomialCoact_expand_mem`, so stability is a statement
about the universal coaction, rather than just the action of rational points. Substitution
`MvPolynomial.expand p` leaves coefficients unchanged; no extraction of pth roots in the
coefficient field is needed. Degree zero is treated separately.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., II.2.16 and II.3.
-/

public section

open scoped TensorProduct

namespace TauCeti.SpecialLinear

universe u

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

attribute [local instance] GeneralLinear.standardComodule standardComodule polynomialComodule

/-- The homogeneous binary forms of degree `p * m` in `x^p` and `y^p`, as a rational
subrepresentation. This construction retains the original coefficient field. -/
noncomputable def frobeniusBinaryForms (m : ℕ) :
    Subcomodule k (coordinateHopfAlgebra k 2) (MvPolynomial (Fin 2) k) :=
  let F : Subcomodule k (coordinateHopfAlgebra k 2) (MvPolynomial (Fin 2) k) :=
    { carrier := (MvPolynomial.expand p).range.toSubmodule
      coact_mem' := by
        rintro _ ⟨f, rfl⟩
        rw [polynomialComodule_coact, AlgHom.toLinearMap_apply]
        exact Comodule.polynomialCoact_expand_mem (coordinateHopfAlgebra k 2)
          (Pi.basisFun k (Fin 2)) p f }
  (F.comap (binaryForms k (p * m)).subtype).map (binaryForms k (p * m)).subtype

variable {k p} in
/-- A Frobenius binary form is homogeneous of degree `p * m` and is a polynomial in the
pth powers of the variables, with coefficients in the original field. -/
@[simp]
theorem mem_frobeniusBinaryForms {m : ℕ} {f : MvPolynomial (Fin 2) k} :
    f ∈ frobeniusBinaryForms k p m ↔
      f.IsHomogeneous (p * m) ∧ ∃ g, MvPolynomial.expand p g = f := by
  simp only [frobeniusBinaryForms, Subcomodule.mem_map, Subcomodule.mem_comap,
    Subcomodule.subtype_apply]
  constructor
  · rintro ⟨⟨f, hf⟩, hg, rfl⟩
    exact ⟨mem_binaryForms.mp hf, hg⟩
  · rintro ⟨hf, hg⟩
    exact ⟨⟨f, mem_binaryForms.mpr hf⟩, hg, rfl⟩

/-- Frobenius binary forms are binary forms of the indicated degree. -/
theorem frobeniusBinaryForms_le (m : ℕ) :
    frobeniusBinaryForms k p m ≤ binaryForms k (p * m) := by
  intro f hf
  exact mem_binaryForms.mpr (mem_frobeniusBinaryForms.mp hf).1

/-- The highest monomial belongs to the Frobenius subrepresentation, including in degree zero. -/
theorem X_one_pow_mem_frobeniusBinaryForms (m : ℕ) :
    (MvPolynomial.X 1 ^ (p * m) : MvPolynomial (Fin 2) k) ∈ frobeniusBinaryForms k p m := by
  refine mem_frobeniusBinaryForms.mpr ⟨MvPolynomial.isHomogeneous_X_pow _ _,
    MvPolynomial.X 1 ^ m, ?_⟩
  simp [pow_mul]

/-- The Frobenius subrepresentation is nonzero in every degree. -/
theorem frobeniusBinaryForms_ne_bot (m : ℕ) : frobeniusBinaryForms k p m ≠ ⊥ := by
  exact Subcomodule.ne_bot_iff.mpr ⟨_, X_one_pow_mem_frobeniusBinaryForms k p m,
    pow_ne_zero _ (MvPolynomial.X_ne_zero 1)⟩

/-- The monomial with `x`-exponent one is absent from the Frobenius
subrepresentation. Its coefficient cannot occur after expansion by `p`. -/
theorem X_zero_mul_X_one_pow_notMem_frobeniusBinaryForms (m : ℕ) :
    (MvPolynomial.X 0 * MvPolynomial.X 1 ^ (p * m - 1) : MvPolynomial (Fin 2) k) ∉
      frobeniusBinaryForms k p m := by
  classical
  intro hf
  obtain ⟨g, hg⟩ := (mem_frobeniusBinaryForms.mp hf).2
  let d : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 (p * m - 1)
  have hd : ¬ p ∣ d 0 := by
    simpa [d] using (Fact.out : p.Prime).not_dvd_one
  have hcoeff := MvPolynomial.coeff_expand_of_not_dvd g hd
  rw [hg] at hcoeff
  have heq : (MvPolynomial.X 0 * MvPolynomial.X 1 ^ (p * m - 1) :
      MvPolynomial (Fin 2) k) = MvPolynomial.monomial d 1 := by
    dsimp only [d]
    rw [MvPolynomial.monomial_single_add, pow_one, ← MvPolynomial.X_pow_eq_monomial]
  rw [heq, MvPolynomial.coeff_monomial, ite_eq_left rfl] at hcoeff
  exact one_ne_zero hcoeff

/-- In positive degree divisible by the characteristic, the Frobenius subrepresentation is
proper. -/
theorem frobeniusBinaryForms_lt {m : ℕ} (hm : 0 < m) :
    frobeniusBinaryForms k p m < binaryForms k (p * m) := by
  refine lt_of_le_of_ne (frobeniusBinaryForms_le k p m) ?_
  intro h
  apply X_zero_mul_X_one_pow_notMem_frobeniusBinaryForms k p m
  rw [h, mem_binaryForms]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hdeg : 1 + (p * m - 1) = p * m := by have := Nat.mul_pos hp hm; omega
  simpa only [hdeg] using
    (MvPolynomial.isHomogeneous_X k (0 : Fin 2)).mul
      (MvPolynomial.isHomogeneous_X_pow (R := k) 1 (p * m - 1))

/-- Binary forms of positive degree divisible by the characteristic are not simple. -/
theorem not_isAtom_binaryForms_mul_char {m : ℕ} (hm : 0 < m) :
    ¬ IsAtom (binaryForms k (p * m)) := by
  intro h
  exact frobeniusBinaryForms_ne_bot k p m (h.2 _ (frobeniusBinaryForms_lt k p hm))

/-- In degree zero the Frobenius subrepresentation is the entire constant representation. -/
@[simp]
theorem frobeniusBinaryForms_zero : frobeniusBinaryForms k p 0 = binaryForms k 0 := by
  apply le_antisymm
  · simpa using frobeniusBinaryForms_le k p 0
  · intro f hf
    have hf0 := mem_binaryForms.mp hf
    have heq : f = MvPolynomial.C (f.coeff 0) :=
      (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp
        ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 2)).mpr hf0)
    rw [mem_frobeniusBinaryForms]
    refine ⟨by simpa using hf0, f, ?_⟩
    rw [heq, MvPolynomial.expand_C]

end TauCeti.SpecialLinear
