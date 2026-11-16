/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GroupLike
public import TauCeti.Topology.Algebra.PointTopology.Basic

/-!
# Continuity of character evaluation on the affine point topology

For any Hopf algebra `H` over `k` and commutative `k`-algebra `R` equipped with a topology,
evaluating convolution points `WithConv (H →ₐ[k] R)` at a group-like element `χ : GroupLike k H` via
`TauCeti.characterValue R χ` is continuous from the evaluation point topology into the units `Rˣ`
with their induced unit/inverse topology: the unit coordinate evaluates at `χ` and the inverse
coordinate evaluates at the antipode `S(χ)`, so no topological-semiring hypothesis on `R` is needed.

## Main declarations

* `TauCeti.continuous_characterValue`: `TauCeti.characterValue R χ` is continuous for every topology
  on `R`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, p. 2.
-/

public section

open TauCeti.PointTopology

namespace TauCeti

variable {k H : Type*} [CommSemiring k] [Semiring H] [HopfAlgebra k H]

/-- Character evaluation is continuous for the point topology and the units topology, for every
topology on the coefficient algebra `R`. -/
@[continuity, fun_prop]
theorem continuous_characterValue (R : Type*) [CommSemiring R] [Algebra k R] [TopologicalSpace R]
    (χ : GroupLike k H) :
    Continuous (characterValue R χ) := by
  rw [Units.continuous_iff]
  exact ⟨(continuous_eval_ofConv (χ : H)).congr fun x ↦ (coe_characterValue_apply R χ x).symm,
    (continuous_eval_ofConv (HopfAlgebra.antipode k (χ : H))).congr fun x ↦
      (coe_inv_characterValue_apply R χ x).symm⟩

end TauCeti
