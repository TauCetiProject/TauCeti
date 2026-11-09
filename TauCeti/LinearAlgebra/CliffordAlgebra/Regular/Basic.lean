/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
public import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Isometry
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Basic

/-!
# The opposite-sign Clifford action on the regular module

The regular module of `CliffordAlgebra Q` has two Clifford actions. Left multiplication
represents `Q`, while the parity-twisted right multiplication
`s ↦ involute s * ι Q v` represents `-Q`. Their vector operators anticommute, and the
second action commutes with left multiplication by every even element, in particular every
Spin element. Thus when `Q` is a negative metric the external positive Clifford action is
compatible with the left Spin action on regular spinors.

This file constructs the second action by Mathlib's Clifford universal property. It proves
its grading, even-element equivariance and isometry naturality, and proves that its vector
operators are symmetric for the scalar-trace pairing `τ (star s * t)`. The latter identity
does not require a definite form or a choice of metric on the Clifford algebra.
For ordered products it computes the reversal and crossing signs; for orthogonal products
these cancel, leaving right multiplication preceded by parity in odd length.

## References

* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules* (1964).
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I.
-/

public section

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)

/-- Right multiplication by a vector, preceded by the grade involution. Its square is
`-Q v`, so for a negative metric it is a positive Clifford generator. -/
def parityTwistedRight : M →ₗ[R] Module.End R (CliffordAlgebra Q) where
  toFun v := (LinearMap.mulRight R (ι Q v)).comp involute.toLinearMap
  map_add' v w := by ext s; simp [mul_add]
  map_smul' r v := by ext s; simp

/-- The parity-twisted right vector operator acts by `s ↦ involute s * ι Q v`. -/
theorem parityTwistedRight_apply (v : M) (s : CliffordAlgebra Q) :
    parityTwistedRight Q v s = involute s * ι Q v :=
  (rfl)

/-- The square of a parity-twisted right vector operator has the opposite quadratic sign. -/
theorem parityTwistedRight_mul_self (v : M) :
    parityTwistedRight Q v * parityTwistedRight Q v =
      algebraMap R (Module.End R (CliffordAlgebra Q)) ((-Q) v) := by
  ext s
  simp [parityTwistedRight_apply, mul_assoc, ι_sq_scalar, Algebra.smul_def,
    Algebra.commutes]

/-- The action of the opposite-sign Clifford algebra on the regular module of `Q`, extending
the operators `s ↦ involute s * ι Q v`. No definiteness or dimension hypothesis is needed. -/
def parityTwistedRightAction :
    CliffordAlgebra (-Q) →ₐ[R] Module.End R (CliffordAlgebra Q) :=
  lift (-Q) ⟨parityTwistedRight Q, parityTwistedRight_mul_self Q⟩

/-- A vector in the opposite-sign Clifford algebra acts by parity-twisted right multiplication. -/
@[simp]
theorem parityTwistedRightAction_ι (v : M) :
    parityTwistedRightAction Q (ι (-Q) v) = parityTwistedRight Q v :=
  lift_ι_apply _ _ _

/-- On an ordered product, the external action is reversal followed by right multiplication,
with the crossing sign and one grade involution for each vector. No orthogonality is needed. -/
theorem parityTwistedRightAction_prod_map_ι (l : List M) (s : CliffordAlgebra Q) :
    parityTwistedRightAction Q (l.map (ι (-Q))).prod s =
      (-1 : R) ^ l.length.choose 2 •
        ((involute : CliffordAlgebra Q → CliffordAlgebra Q)^[l.length] s *
          reverse (l.map (ι Q)).prod) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, mul_apply_eq_comp,
      parityTwistedRightAction_ι, parityTwistedRight_apply, ih]
    -- The new vector crosses all previous factors, adding their length to the sign exponent.
    have hchoose : (l.length + 1).choose 2 = l.length + l.length.choose 2 := by
      simp [Nat.choose_succ_succ]
    simp only [map_smul, map_mul, ← reverse_involute, involute_prod_map_ι,
      mul_smul_comm, smul_mul_assoc, smul_smul, List.map_cons, List.prod_cons,
      reverse.map_mul, reverse_ι, List.length_cons, Function.iterate_succ_apply',
      hchoose, pow_add, mul_assoc]
    rw [mul_comm ((-1 : R) ^ l.length.choose 2)]

/-- For an orthogonal ordered product the reversal and crossing signs cancel. -/
theorem parityTwistedRightAction_prod_map_ι_of_pairwise_isOrtho {l : List M}
    (hl : l.Pairwise Q.IsOrtho) (s : CliffordAlgebra Q) :
    parityTwistedRightAction Q (l.map (ι (-Q))).prod s =
      (involute : CliffordAlgebra Q → CliffordAlgebra Q)^[l.length] s *
        (l.map (ι Q)).prod := by
  rw [parityTwistedRightAction_prod_map_ι, reverse_prod_map_ι_of_pairwise_isOrtho hl,
    mul_smul_comm, smul_smul, ← mul_pow]
  simp

/-- An even orthogonal product in the external algebra acts by right multiplication
by the same ordered product in the original algebra. -/
theorem parityTwistedRightAction_prod_map_ι_of_even {l : List M}
    (hl : l.Pairwise Q.IsOrtho) (hlen : Even l.length) (s : CliffordAlgebra Q) :
    parityTwistedRightAction Q (l.map (ι (-Q))).prod s = s * (l.map (ι Q)).prod := by
  rw [parityTwistedRightAction_prod_map_ι_of_pairwise_isOrtho Q hl,
    involute_involutive.iterate_even hlen, Function.id_def]

/-- An odd orthogonal product in the external algebra acts by parity followed by right
multiplication by the same ordered product in the original algebra. -/
theorem parityTwistedRightAction_prod_map_ι_of_odd {l : List M}
    (hl : l.Pairwise Q.IsOrtho) (hlen : Odd l.length) (s : CliffordAlgebra Q) :
    parityTwistedRightAction Q (l.map (ι (-Q))).prod s = involute s * (l.map (ι Q)).prod := by
  rw [parityTwistedRightAction_prod_map_ι_of_pairwise_isOrtho Q hl,
    involute_involutive.iterate_odd hlen]

/-- The external vector operators are odd for the grade involution of the regular module. -/
theorem involute_parityTwistedRight (v : M) (s : CliffordAlgebra Q) :
    involute (parityTwistedRight Q v s) = -parityTwistedRight Q v (involute s) := by
  simp [parityTwistedRight_apply]

/-- Left Clifford vectors anticommute with the external opposite-sign vector operators. -/
theorem parityTwistedRight_ι_mul (v w : M) (s : CliffordAlgebra Q) :
    parityTwistedRight Q v (ι Q w * s) = -(ι Q w * parityTwistedRight Q v s) := by
  simp [parityTwistedRight_apply, mul_assoc]

/-- Parity-twisted right multiplication commutes with left multiplication by an even element. -/
theorem parityTwistedRight_even_mul (v : M) {a : CliffordAlgebra Q}
    (ha : a ∈ evenOdd Q 0) (s : CliffordAlgebra Q) :
    parityTwistedRight Q v (a * s) = a * parityTwistedRight Q v s := by
  simp [parityTwistedRight_apply, involute_eq_of_mem_even ha, mul_assoc]

/-- The full external Clifford action commutes with left multiplication by an even element. -/
theorem parityTwistedRightAction_even_mul (x : CliffordAlgebra (-Q))
    {a : CliffordAlgebra Q} (ha : a ∈ evenOdd Q 0) (s : CliffordAlgebra Q) :
    parityTwistedRightAction Q x (a * s) = a * parityTwistedRightAction Q x s := by
  induction x using CliffordAlgebra.induction generalizing s with
  | algebraMap r => simp [Algebra.smul_def, Algebra.commutes, mul_assoc]
  | ι v => simpa using parityTwistedRight_even_mul Q v ha s
  | add x y hx hy => simp [hx, hy, mul_add]
  | mul x y hx hy => simp [hx, hy]

/-- The external opposite-sign Clifford action is equivariant for the left regular Spin action. -/
theorem parityTwistedRightAction_spin_mul (x : CliffordAlgebra (-Q))
    (g : spinGroup Q) (s : CliffordAlgebra Q) :
    parityTwistedRightAction Q x ((g : CliffordAlgebra Q) * s) =
      (g : CliffordAlgebra Q) * parityTwistedRightAction Q x s :=
  parityTwistedRightAction_even_mul Q x (spinGroup.mem_even g.property) s

/-- Parity on the regular module intertwines the external action with its grade involution. -/
theorem involute_parityTwistedRightAction (x : CliffordAlgebra (-Q)) (s : CliffordAlgebra Q) :
    involute (parityTwistedRightAction Q x s) =
      parityTwistedRightAction Q (involute x) (involute s) := by
  induction x using CliffordAlgebra.induction generalizing s with
  | algebraMap r => simp
  | ι v => simp [involute_parityTwistedRight]
  | add x y hx hy => simp [hx, hy]
  | mul x y hx hy => simp [hx, hy]

section Trace

variable [Invertible (2 : R)]

/-- The external vector operators are symmetric for the Clifford scalar-trace pairing.
For a negative definite real form this is the symmetry equation for the positive regular
spinor metric. -/
theorem scalarTrace_star_parityTwistedRight_mul (v : M) (s t : CliffordAlgebra Q) :
    scalarTrace Q (star (parityTwistedRight Q v s) * t) =
      scalarTrace Q (star s * parityTwistedRight Q v t) := by
  have hstar : star (involute s) = reverse s := by simp [star_def]
  simp only [parityTwistedRight_apply, star_mul, star_ι, hstar, neg_mul, map_neg]
  rw [mul_assoc, scalarTrace_mul_comm]
  conv_lhs => arg 1; rw [← scalarTrace_involute]
  simp [star_def, reverse_involute, mul_assoc]

/-- Reversion in the external Clifford algebra is adjunction for its action with respect to
the scalar-trace pairing. In particular, its vector operators are symmetric, even though
left multiplication by a vector is skew-symmetric for the same pairing. -/
theorem scalarTrace_star_parityTwistedRightAction_mul
    (x : CliffordAlgebra (-Q)) (s t : CliffordAlgebra Q) :
    scalarTrace Q (star (parityTwistedRightAction Q x s) * t) =
      scalarTrace Q (star s * parityTwistedRightAction Q (reverse x) t) := by
  induction x using CliffordAlgebra.induction generalizing s t with
  | algebraMap r => simp [star_smul]
  | ι v => simpa using scalarTrace_star_parityTwistedRight_mul Q v s t
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | mul x y hx hy => simp [hx, hy]

end Trace

section Naturality

variable {N : Type*} [AddCommGroup N] [Module R N] {Q' : QuadraticForm R N}

/-- The vector operators are natural under quadratic isometries. -/
theorem map_parityTwistedRight (f : Q →qᵢ Q') (v : M) (s : CliffordAlgebra Q) :
    map f (parityTwistedRight Q v s) = parityTwistedRight Q' (f v) (map f s) := by
  simp [parityTwistedRight_apply]

/-- The full external action is natural under quadratic isometries, using the same linear
isometry for the negatives of the forms. -/
theorem map_parityTwistedRightAction (f : Q →qᵢ Q') (x : CliffordAlgebra (-Q))
    (s : CliffordAlgebra Q) :
    map f (parityTwistedRightAction Q x s) =
      parityTwistedRightAction Q' (map f.neg x) (map f s) := by
  induction x using CliffordAlgebra.induction generalizing s with
  | algebraMap r => simp
  | ι v => simp [map_parityTwistedRight]
  | add x y hx hy => simp [hx, hy]
  | mul x y hx hy => simp [hx, hy]

end Naturality

end CliffordAlgebra
