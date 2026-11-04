/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Reindex

/-!
# The zero-weight part for the fixed Cartan

For a positive definite even Gram matrix with nonpositive off-diagonal entries, the Cartan
vectors fixed by a diagram permutation separate every root line of the signed shell Lie
algebra. In fact, one integral Cartan vector suffices: Cramer's rule applied to the constant
vector gives a diagram-invariant vector whose pairing with a root is the determinant times
its height. The height is nonzero because all simple-root coordinates have one sign.

Consequently the centralizer of the fixed Cartan in the integral shell algebra is exactly
the ambient Cartan. Inside the fixed algebra its centralizer is exactly the fixed Cartan.
These statements concern ordinary commuting vectors over the integers, not generalized
weight spaces or arbitrary scalar extensions.

The construction uses the signed shell algebra and its relabelling action from the imported
modules, and Mathlib's `Matrix.cramer` and `Matrix.mulVec_cramer`.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §§7.8–7.9.
-/

public section

namespace Matrix.ShellLieAlgebra

variable {I : Type*} [Fintype I] [LinearOrder I] {B : Matrix I I ℤ}

/-- A vector commuting with every diagram-fixed Cartan vector has no root component. The
converse holds without any root-system hypotheses. -/
theorem forall_fixed_cartan_lie_eq_zero_iff (hB : B.PosDef) (hev : ∀ i, Even (B i i))
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (σ : Equiv.Perm I) (hσ : B.reindex σ σ = B)
    (x : ShellLieAlgebra B) :
    (∀ h : I → ℤ, h ∘ σ.symm = h → ⁅cartan B h, x⁆ = 0) ↔
      (equivProd B x).2 = 0 := by
  constructor
  · intro hx
    obtain ⟨h, hh, hreg⟩ := hB.exists_invariant_pairing_ne_zero hev hoff σ hσ
    ext a
    have ha := congrArg (fun y ↦ (equivProd B y).2 a) (hx h hh)
    rw [equivProd_cartan_lie_snd] at ha
    have hmul : (h ⬝ᵥ B *ᵥ (a : I → ℤ)) * (equivProd B x).2 a = 0 := by
      simpa using ha
    exact (mul_eq_zero.mp hmul).resolve_left (hreg a)
  · intro hx h _
    have heq := (equivProd_snd_eq_zero_iff B x).mp hx
    rw [heq, cartan_lie_cartan]

/-- The zero-weight part inside the diagram-fixed shell algebra is precisely the fixed Cartan. -/
theorem exists_fixed_cartan_eq_iff (hB : B.PosDef) (hev : ∀ i, Even (B i i))
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (σ : Equiv.Perm I) (hσ : B.reindex σ σ = B)
    (x : ShellLieAlgebra B) (hx : reindex σ hσ x = x) :
    (∃ h : I → ℤ, h ∘ σ.symm = h ∧ x = cartan B h) ↔
      ∀ h : I → ℤ, h ∘ σ.symm = h → ⁅cartan B h, x⁆ = 0 := by
  constructor
  · rintro ⟨h, _, rfl⟩ k _
    exact cartan_lie_cartan k h
  · intro hzero
    have hroot := (forall_fixed_cartan_lie_eq_zero_iff hB hev hoff σ hσ x).mp hzero
    have heq := (equivProd_snd_eq_zero_iff B x).mp hroot
    refine ⟨(equivProd B x).1, ?_, heq⟩
    rw [heq, reindex_cartan] at hx
    simpa only [equivProd_cartan] using congrArg (fun y ↦ (equivProd B y).1) hx

end Matrix.ShellLieAlgebra
