/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.ChevalleyBasis
public import TauCeti.RingTheory.DividedPowers.NormalOrdering

/-!
# Non-opposite root straightening for the signed shell Lie algebra

The normalized root vectors of the signed norm-two shell have integral structure constants
`N(a,b) = ±1`. This file computes the divided-power straightening coefficients for every
non-opposite pair, in any associative rational algebra receiving a Lie homomorphism from the
integral shell algebra. Thus the formulas apply both in enveloping algebras and in their
representations, without a nilpotence or faithfulness assumption.

If `a + b` is a root, the formula is

```text
e_a⁽ᵐ⁾ e_b⁽ⁿ⁾ = ∑ k ≤ min(m,n), N(a,b)^k • (e_b⁽ⁿ⁻ᵏ⁾ e_(a+b)⁽ᵏ⁾ e_a⁽ᵐ⁻ᵏ⁾).
```

The two roots commute with their sum: their pairings with it are both one. Consequently the
class-two normal-ordering rule applies, and integer scaling extracts the displayed sign. If the
sum is neither a root nor zero, the two divided powers commute. These cover all different-root
straightening cases in a simply laced root system except opposite roots; opposite roots require
the separate rank-one formula with Cartan binomials.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.8, for the signed shell model.
-/

public section

namespace Matrix.ShellLieAlgebra

open TauCeti.Associative

variable {I : Type*} [Fintype I] [LinearOrder I] {B : Matrix I I ℤ}
variable {A : Type*} [Ring A] [Algebra ℚ A]

attribute [local instance] LieRing.ofAssociativeRing

/-- **Integral non-opposite root straightening.** If `a + b` is a root, the coefficients for
reordering the divided powers of their normalized root vectors are the integer signs
`N(a,b)^k`. The formula holds under any Lie homomorphism into an associative rational algebra. -/
theorem dividedPower_normalizedRoot_mul_of_add_mem (hB : B.PosDef)
    (hev : ∀ i, Even (B i i)) {a b : B.normTwoShell}
    (hab : (a : I → ℤ) + b ∈ B.normTwoShell) :
    letI := lieRing hB hev
    ∀ (ρ : ShellLieAlgebra B →ₗ⁅ℤ⁆ A) (m n : ℕ),
      dividedPower m (ρ (normalizedRoot B a)) * dividedPower n (ρ (normalizedRoot B b)) =
        ∑ k ∈ Finset.range (min m n + 1),
          ((structureConstant B a b : ℤ) ^ k) •
            (dividedPower (n - k) (ρ (normalizedRoot B b)) *
              dividedPower k (ρ (normalizedRoot B ⟨_, hab⟩)) *
              dividedPower (m - k) (ρ (normalizedRoot B a))) := by
  let _ := lieRing hB hev
  intro ρ m n
  have hS := hB.isHermitian.isSymm
  have hp : (a : I → ℤ) ⬝ᵥ B *ᵥ b = -1 := (hS.add_mem_normTwoShell_iff a.2 b.2).mp hab
  have hpa : 0 ≤ (a : I → ℤ) ⬝ᵥ B *ᵥ ((a : I → ℤ) + b) := by
    rw [mulVec_add, dotProduct_add, mem_normTwoShell.mp a.2, hp]
    norm_num
  have hpb : 0 ≤ (b : I → ℤ) ⬝ᵥ B *ᵥ ((a : I → ℤ) + b) := by
    rw [mulVec_add, dotProduct_add, hS.dotProduct_mulVec_comm (x := (b : I → ℤ)) (y := a),
      mem_normTwoShell.mp b.2, hp]
    norm_num
  -- The sum root commutes with both original roots, before applying the representation.
  have hc (r : B.normTwoShell) (hr : 0 ≤ (r : I → ℤ) ⬝ᵥ B *ᵥ ((a : I → ℤ) + b)) :
      Commute (ρ (normalizedRoot B r)) (ρ (normalizedRoot B ⟨_, hab⟩)) := by
    apply (commute_iff_lie_eq).mpr
    rw [← ρ.map_lie]
    rw [normalizedRoot_lie_normalizedRoot r ⟨_, hab⟩]
    rw [rootBracket_eq_zero_of_nonneg hS (a := r) (b := ⟨_, hab⟩) hr,
      smul_zero, map_zero]
  have hxy : ρ (normalizedRoot B a) * ρ (normalizedRoot B b) =
      ρ (normalizedRoot B b) * ρ (normalizedRoot B a) +
        (structureConstant B a b : ℤ) • ρ (normalizedRoot B ⟨_, hab⟩) := by
    have h := congrArg ρ (normalizedRoot_lie_normalizedRoot_of_mem hab)
    simp only [ρ.map_lie, Units.smul_def, map_smul, Ring.lie_def] at h
    exact (sub_eq_iff_eq_add').mp h
  rw [dividedPower_mul_dividedPower_of_commutator_eq hxy
    ((hc a hpa).smul_right _) ((hc b hpb).smul_right _)]
  apply Finset.sum_congr rfl
  intro k _
  rw [dividedPower_zsmul, mul_smul_comm, smul_mul_assoc]

/-- Normalized root divided powers commute when the sum of the roots is neither a root nor
zero. Together with `dividedPower_normalizedRoot_mul_of_add_mem`, this covers every
non-opposite root pair. -/
theorem dividedPower_normalizedRoot_mul_comm_of_add_notMem_of_add_ne_zero (hB : B.PosDef)
    (hev : ∀ i, Even (B i i)) {a b : B.normTwoShell}
    (hab : (a : I → ℤ) + b ∉ B.normTwoShell) (hne : (a : I → ℤ) + b ≠ 0) :
    letI := lieRing hB hev
    ∀ (ρ : ShellLieAlgebra B →ₗ⁅ℤ⁆ A) (m n : ℕ),
      dividedPower m (ρ (normalizedRoot B a)) * dividedPower n (ρ (normalizedRoot B b)) =
        dividedPower n (ρ (normalizedRoot B b)) * dividedPower m (ρ (normalizedRoot B a)) := by
  let _ := lieRing hB hev
  intro ρ m n
  have hcomm : Commute (ρ (normalizedRoot B a)) (ρ (normalizedRoot B b)) := by
    rw [commute_iff_lie_eq, ← ρ.map_lie,
      normalizedRoot_lie_normalizedRoot_of_notMem_of_add_ne_zero hab hne, map_zero]
  exact (commute_dividedPower_dividedPower hcomm m n).eq

end Matrix.ShellLieAlgebra
