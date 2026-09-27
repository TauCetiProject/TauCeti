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

/-- The torus triple is imprimitive: `{0, 2}` is a nontrivial block. -/
theorem isPreprimitiveBool_torusTriple : torusTriple.isPreprimitiveBool = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact not_isPreprimitive_torusTriple ((isPreprimitiveBool_eq_true_iff _).mp h)

/-- The degree-three symmetric triple is primitive. -/
theorem isPreprimitiveBool_s3Triple : s3Triple.isPreprimitiveBool = true := by
  apply (isPreprimitiveBool_eq_true_iff _).mpr
  exact @IsPreprimitive.of_prime_card _ _ _ _ isConnected_s3Triple.isPretransitive
    (by simpa using (by decide : Nat.Prime 3))

/-- The degree-one triple is primitive. -/
theorem isPreprimitiveBool_cyclicTriple_one : (cyclicTriple 1).isPreprimitiveBool = true := by
  apply (isPreprimitiveBool_eq_true_iff _).mpr
  exact IsPreprimitive.of_subsingleton

end PermutationTriple

end TauCeti
