/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Word

/-!
# Checked derivation steps for M11 relations

A step multiplies rotations or inverses of two known relations, then compares
free reductions with a conjugate of a variant of the output word. This records
only the inputs, output, transformations and conjugator; intermediate words need
not be repeated in the certificate.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations

/-- Rotation preserves and reflects the identity relation. -/
theorem eval_rotate_eq_one_iff (w : Word) (n : ℕ) :
    eval (w.rotate n) = 1 ↔ eval w = 1 := by
  constructor
  · intro h
    have hw := List.rotate_eq_iff.mp (show w.rotate n = w.rotate n from rfl)
    rw [hw]
    exact eval_rotate_eq_one h _
  · intro h
    exact eval_rotate_eq_one h n

/-- Inversion and rotation preserve and reflect the identity relation. -/
theorem eval_variant_eq_one_iff (w : Word) (invert : Bool) (shift : ℕ) :
    eval (variant w invert shift) = 1 ↔ eval w = 1 := by
  cases invert <;> simp [variant, eval_rotate_eq_one_iff, eval_invRev]

/-- A checked free reduction proves the output relation from two input relations. -/
theorem variant_product_eq_one {u v w : Word}
    (hu : eval u = 1) (hv : eval v = 1)
    (left right result : Bool × ℕ) (q : Word)
    (hred : FreeGroup.reduce (variant u left.1 left.2 ++ variant v right.1 right.2) =
      FreeGroup.reduce (q ++ variant w result.1 result.2 ++ FreeGroup.invRev q)) :
    eval w = 1 := by
  apply (eval_variant_eq_one_iff w result.1 result.2).mp
  apply reduced_conjugate_eq_one q ?_ hred
  exact product_eq_one
    ((eval_variant_eq_one_iff u left.1 left.2).mpr hu)
    ((eval_variant_eq_one_iff v right.1 right.2).mpr hv)

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations
