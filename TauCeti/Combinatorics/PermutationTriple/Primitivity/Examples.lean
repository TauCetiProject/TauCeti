/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Primitivity.Basic
public import TauCeti.Combinatorics.PermutationTriple.Examples

/-!
# Examples of deciding primitivity of permutation triples

The torus triple is imprimitive, while the degree-three symmetric triple and the degree-one
triple are primitive. These check the finite test against concrete monodromy actions.
-/

public section

namespace TauCeti

namespace PermutationTriple

open MulAction

/-- The torus triple is not primitive: `{0, 2}` is a nontrivial block. -/
theorem not_isPrimitive_torusTriple : ¬ torusTriple.IsPrimitive := fun h =>
  not_isPreprimitive_torusTriple ((isPrimitive_iff _).mp h)

/-- The torus triple is imprimitive: `{0, 2}` is a nontrivial block. -/
theorem isPrimitiveBool_torusTriple : torusTriple.isPrimitiveBool = false :=
  Bool.eq_false_iff.mpr fun h =>
    not_isPrimitive_torusTriple ((isPrimitiveBool_eq_true_iff _).mp h)

/-- The degree-three symmetric triple is primitive, since its degree is prime. -/
theorem isPrimitive_s3Triple : s3Triple.IsPrimitive :=
  (isPrimitive_iff _).mpr <|
    @IsPreprimitive.of_prime_card _ _ _ _ isConnected_s3Triple.isPretransitive
      (by simpa using (by decide : Nat.Prime 3))

/-- The degree-three symmetric triple is primitive. -/
theorem isPrimitiveBool_s3Triple : s3Triple.isPrimitiveBool = true :=
  (isPrimitiveBool_eq_true_iff _).mpr isPrimitive_s3Triple

/-- The degree-one triple is primitive. -/
theorem isPrimitiveBool_cyclicTriple_one : (cyclicTriple 1).isPrimitiveBool = true := by
  apply (isPrimitiveBool_eq_true_iff _).mpr
  apply (isPrimitive_iff _).mpr
  exact IsPreprimitive.of_subsingleton

end PermutationTriple

end TauCeti
