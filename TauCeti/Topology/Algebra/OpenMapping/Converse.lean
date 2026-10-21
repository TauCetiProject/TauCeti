/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic
public import TauCeti.Topology.Algebra.IsUniformGroup.Quotient
public import TauCeti.Topology.Algebra.ZeroSequenceOfUnits

/-!
# The remaining implications of Banach's theorem for Tate rings

Wedhorn's Theorem 6.16 says that, for an `A`-linear map `u : M → N` out of a complete
first-countable module over a ring with a zero sequence of units, any two of *(a) `N` is complete*,
*(b) `u` is surjective* and *(c) `u` is open* imply the third. That (a) and (b) imply (c) is
Henkel's open mapping theorem, `TauCeti.HasZeroSequenceOfUnits.isOpenMap`, in the sibling file
`TauCeti.Topology.Algebra.OpenMapping.Henkel`. The other two implications are proved here.

Both rest on Mathlib's `Submodule.eq_top_of_nonempty_interior'`: when zero is a limit of units
(the instance `TauCeti.HasZeroSequenceOfUnits.nhdsWithin_isUnit_neBot`), a submodule with nonempty
interior is everything. An open linear map therefore has an open, hence full, range, so (c) alone
implies (b). A continuous open linear map is then an open quotient map, so its target is complete
by `IsOpenQuotientMap.completeSpace`: (c) implies (a) for continuous `u`.

## Main results

* `LinearMap.surjective_of_isOpenMap`: an open linear map is surjective.
* `LinearMap.completeSpace_of_isOpenMap`: a continuous open linear map out of a complete
  first-countable module has a complete target.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Theorem 6.16.
-/

public section

open Filter Topology
open scoped Uniformity

namespace LinearMap

variable {A : Type*} [Ring A] [TopologicalSpace A] [TauCeti.HasZeroSequenceOfUnits A]

variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- **An open linear map is surjective** over a ring with a zero sequence of units
([Wedhorn, *Adic Spaces*][wedhorn_adic], Theorem 6.16, *(c) ⇒ (b)*). No topology on `M` is
involved beyond the openness of `f`. -/
theorem surjective_of_isOpenMap [TopologicalSpace M] [TopologicalSpace N] [ContinuousAdd N]
    [ContinuousSMul A N] (f : M →ₗ[A] N) (hf : IsOpenMap f) : Function.Surjective f := by
  -- The range is an open submodule, so it has nonempty interior.
  refine LinearMap.range_eq_top.mp <| Submodule.eq_top_of_nonempty_interior' _ ⟨0, ?_⟩
  rw [LinearMap.coe_range, hf.isOpen_range.interior_eq]
  exact ⟨0, map_zero f⟩

/-- **A continuous open linear map out of a complete first-countable module has a complete
target** over a ring with a zero sequence of units ([Wedhorn, *Adic Spaces*][wedhorn_adic],
Theorem 6.16, *(b) and (c) ⇒ (a)*). -/
theorem completeSpace_of_isOpenMap [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
    [(𝓤 M).IsCountablyGenerated] [UniformSpace N] [IsUniformAddGroup N] [ContinuousSMul A N]
    (f : M →ₗ[A] N) (hfc : Continuous f) (hf : IsOpenMap f) : CompleteSpace N :=
  -- `f` is surjective, hence an open quotient map out of a complete first-countable group.
  IsOpenQuotientMap.completeSpace (f := f) ⟨f.surjective_of_isOpenMap hf, hfc, hf⟩

end LinearMap
