/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Graded.Sign
public import TauCeti.Geometry.Convex.Cone.Chamber

/-!
# Sign subalgebras in strict dual chambers

A continuous real functional in the positive (respectively negative) chamber of an additive
monoid `P` takes one sign on every nonzero degree in `P`. Hence for a Lie algebra graded over `P`,
with zero pieces outside the nonzero elements of `P`, the positive (respectively negative) sign
subalgebra of the functional is the whole Lie algebra.

## Main results

* `TauCeti.signSubalgebra_pos_eq_top_of_mem_positiveChamber`
* `TauCeti.signSubalgebra_neg_eq_top_of_mem_negativeChamber`
-/

public section

namespace TauCeti

variable {N V R L : Type*} [AddCommMonoid N] [DecidableEq N] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [CommRing R] [LieRing L] [LieAlgebra R L]
  {P : AddSubmonoid N} {i : N →+ V} (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ]
  (hℒ : ∀ n, ℒ n ≠ ⊥ → n ∈ P ∧ n ≠ 0) {θ : V →L[ℝ] ℝ}

include hℒ in
/-- If the nonzero pieces of a graded Lie algebra lie in the nonzero part of `P`, a functional in
the positive chamber of `P` has the whole Lie algebra as its positive sign subalgebra. -/
theorem signSubalgebra_pos_eq_top_of_mem_positiveChamber (hθ : θ ∈ P.positiveChamber i) :
    signSubalgebra ℒ (θ.toLinearMap.toAddMonoidHom.comp i) SignType.pos = ⊤ :=
  signSubalgebra_eq_top_of_sign_eq ℒ _ _ fun n hn =>
    sign_eq_one_iff.mpr ((P.mem_positiveChamber i).mp hθ n (hℒ n hn).1 (hℒ n hn).2)

include hℒ in
/-- If the nonzero pieces of a graded Lie algebra lie in the nonzero part of `P`, a functional in
the negative chamber of `P` has the whole Lie algebra as its negative sign subalgebra. -/
theorem signSubalgebra_neg_eq_top_of_mem_negativeChamber (hθ : θ ∈ P.negativeChamber i) :
    signSubalgebra ℒ (θ.toLinearMap.toAddMonoidHom.comp i) SignType.neg = ⊤ :=
  signSubalgebra_eq_top_of_sign_eq ℒ _ _ fun n hn =>
    sign_eq_neg_one_iff.mpr ((P.mem_negativeChamber i).mp hθ n (hℒ n hn).1 (hℒ n hn).2)

end TauCeti
