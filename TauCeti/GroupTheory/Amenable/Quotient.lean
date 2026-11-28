/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Discrete
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.QuotientKerEquiv
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Quotients and images of amenable groups

The target of a continuous homomorphism `φ : G →ₜ* H` with dense range out of an amenable
topological group is amenable (`TauCeti.Amenable.of_denseRange`): the pushforward
`f ↦ m (f ∘ φ)` of a left-invariant mean `m` on `UCB G` is a left-invariant mean on `UCB H`. This
file applies that principle to quotients and to ranges.

The quotient `G ⧸ N` of an amenable topological group by a normal subgroup `N`, with the quotient
topology, is amenable. The subgroup `N` need not be closed, so `G ⧸ N` need not be Hausdorff. The
range of a continuous homomorphism out of an amenable topological group, with the subspace
topology, is amenable. Every homomorphism out of a discrete group is continuous, so the range of
any homomorphism out of an amenable discrete group is amenable.

The range of a continuous homomorphism `φ` is also the image of `G ⧸ φ.ker` under the continuous
surjective homomorphism `QuotientGroup.rangeKerLift φ`, so amenability of `G ⧸ φ.ker` alone implies
amenability of `φ.range`, with no amenability assumption on `G`. The quotient carries the quotient
topology and the range the subspace topology, so the first isomorphism theorem
`QuotientGroup.quotientKerEquivRange φ` need not be a homeomorphism. It is one exactly when `φ` is a
strict map (Mathlib's `Topology.IsStrictMap`), and then the two groups are amenable together.

For a homomorphism `φ : G →* H` of discrete groups, the first isomorphism theorem
`QuotientGroup.quotientKerEquivRange` is an isomorphism of discrete groups. Hence `G ⧸ φ.ker` is
amenable exactly when the image `φ.range` is, and, for surjective `φ`, exactly when `H` is. These
statements make no amenability assumption on `G`.

## Main results

* `TauCeti.Amenable.quotient`, `TauCeti.AddAmenable.quotient`: a quotient of an amenable
  topological group is amenable.
* `TauCeti.Amenable.range`, `TauCeti.AddAmenable.range`: the range of a continuous homomorphism
  out of an amenable topological group is amenable.
* `TauCeti.Amenable.range_of_quotient_ker`, `TauCeti.AddAmenable.range_of_quotient_ker`: if `φ` is
  continuous and `G ⧸ φ.ker` is amenable, then `φ.range` is amenable.
* `TauCeti.amenable_quotient_ker_iff_range_of_isStrictMap`,
  `TauCeti.addAmenable_quotient_ker_iff_range_of_isStrictMap`: for a strict homomorphism `φ`, the
  groups `G ⧸ φ.ker` and `φ.range` are amenable together.
* `TauCeti.Amenable.range_of_discreteTopology`,
  `TauCeti.AddAmenable.range_of_discreteTopology`: the range of a homomorphism out of an amenable
  discrete group is amenable, for every group topology on the target.
* `TauCeti.Mean.mapOfDiscrete_quotientKerEquivRange`,
  `TauCeti.AddMean.mapOfDiscrete_quotientKerEquivRange`: pushing forward a discrete mean along the
  quotient-by-kernel isomorphism agrees with pushing forward directly to the range.
* `TauCeti.amenable_quotient_ker_iff_range`, `TauCeti.amenable_quotient_ker_iff_of_surjective`,
  `TauCeti.addAmenable_quotient_ker_iff_range`, and
  `TauCeti.addAmenable_quotient_ker_iff_of_surjective`: for homomorphisms of discrete groups,
  amenability of the quotient by the kernel is amenability of the image.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Proposition G.2.2.
* A. Garrido, *An introduction to amenable groups*, Proposition 2.2.
-/

public section

open Topology

namespace TauCeti

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The quotient of an amenable topological group by a normal subgroup, with the quotient
topology, is amenable. -/
instance Amenable.quotient [Amenable G] (N : Subgroup G) [N.Normal] : Amenable (G ⧸ N) :=
  .of_denseRange (Subgroup.quotientMkContinuousMonoidHom N) <| Function.Surjective.denseRange
    fun q => QuotientGroup.induction_on q fun g => ⟨g, N.quotientMkContinuousMonoidHom_apply g⟩

/-- The range of a continuous homomorphism out of an amenable topological group, with the subspace
topology, is amenable. -/
theorem Amenable.range [Amenable G] (φ : G →ₜ* H) : Amenable φ.range :=
  .of_denseRange ⟨φ.rangeRestrict, φ.continuous.subtype_mk _⟩
    φ.rangeRestrict_surjective.denseRange

/-- If `φ : G →* H` is continuous and the quotient `G ⧸ φ.ker` is amenable, then the range of `φ`
is amenable for the subspace topology. -/
theorem Amenable.range_of_quotient_ker {φ : G →* H} (hφ : Continuous φ) [Amenable (G ⧸ φ.ker)] :
    Amenable φ.range :=
  .of_denseRange ⟨QuotientGroup.rangeKerLift φ, QuotientGroup.continuous_rangeKerLift hφ⟩
    (QuotientGroup.rangeKerLift_surjective φ).denseRange

/-- For a strict homomorphism `φ : G →* H`, the quotient `G ⧸ φ.ker` with the quotient topology is
amenable exactly when the range of `φ` with the subspace topology is. -/
theorem amenable_quotient_ker_iff_range_of_isStrictMap {φ : G →* H} (hφ : IsStrictMap φ) :
    Amenable (G ⧸ φ.ker) ↔ Amenable φ.range :=
  (ContinuousMulEquiv.quotientKerEquivRange hφ).amenable_iff

section DiscreteTopology

variable [DiscreteTopology G]

/-- The range of a homomorphism out of an amenable discrete group is amenable, for every group
topology on the target. -/
instance Amenable.range_of_discreteTopology [Amenable G] (φ : G →* H) : Amenable φ.range :=
  .of_surjective φ.rangeRestrict φ.rangeRestrict_surjective

/-- Pushing forward a mean on a discrete group along the quotient-by-kernel isomorphism agrees with
pushing forward directly to the range. -/
@[to_additive
  /-- Pushing forward an additive mean on a discrete additive group along the quotient-by-kernel
  isomorphism agrees with pushing forward directly to the range. -/]
theorem Mean.mapOfDiscrete_quotientKerEquivRange (φ : G →* H) (m : Mean G) :
    letI := QuotientGroup.discreteTopology (isOpen_discrete (φ.ker : Set G))
    (m.mapOfDiscrete (QuotientGroup.mk' φ.ker)).mapOfDiscrete
        (QuotientGroup.quotientKerEquivRange φ) =
      m.mapOfDiscrete φ.rangeRestrict := by
  have := QuotientGroup.discreteTopology (isOpen_discrete (φ.ker : Set G))
  rw [Mean.mapOfDiscrete_mapOfDiscrete]
  exact congrArg (m.mapOfDiscrete ·)
    (funext (TauCeti.QuotientGroup.quotientKerEquivRange_apply_mk φ))

/-- For a homomorphism `φ` of discrete groups, the quotient `G ⧸ φ.ker` is amenable exactly when
the image `φ.range` is. -/
theorem amenable_quotient_ker_iff_range [DiscreteTopology H] (φ : G →* H) :
    Amenable (G ⧸ φ.ker) ↔ Amenable φ.range := by
  have := QuotientGroup.discreteTopology (isOpen_discrete (φ.ker : Set G))
  exact (QuotientGroup.quotientKerEquivRange φ).amenable_iff_of_discreteTopology

/-- For a surjective homomorphism `φ : G →* H` of discrete groups, the quotient `G ⧸ φ.ker` is
amenable exactly when `H` is. -/
theorem amenable_quotient_ker_iff_of_surjective [DiscreteTopology H] {φ : G →* H}
    (hφ : Function.Surjective φ) : Amenable (G ⧸ φ.ker) ↔ Amenable H := by
  have := QuotientGroup.discreteTopology (isOpen_discrete (φ.ker : Set G))
  exact (QuotientGroup.quotientKerEquivOfSurjective φ hφ).amenable_iff_of_discreteTopology

end DiscreteTopology

section Additive

variable {A B : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

/-- The quotient of an amenable additive topological group by a normal additive subgroup, with the
quotient topology, is amenable. -/
instance AddAmenable.quotient [AddAmenable A] (N : AddSubgroup A) [N.Normal] :
    AddAmenable (A ⧸ N) :=
  .of_denseRange ⟨QuotientAddGroup.mk' N, continuous_quot_mk⟩
    (QuotientAddGroup.mk'_surjective N).denseRange

attribute [to_additive existing] Amenable.quotient

/-- The range of a continuous additive homomorphism out of an amenable additive topological group,
with the subspace topology, is amenable. -/
theorem AddAmenable.range [AddAmenable A] (φ : A →ₜ+ B) : AddAmenable φ.range :=
  .of_denseRange ⟨φ.rangeRestrict, φ.continuous.subtype_mk _⟩
    φ.rangeRestrict_surjective.denseRange

attribute [to_additive existing] Amenable.range

/-- If `φ : A →+ B` is continuous and the quotient `A ⧸ φ.ker` is amenable, then the range of `φ`
is amenable for the subspace topology. -/
theorem AddAmenable.range_of_quotient_ker {φ : A →+ B} (hφ : Continuous φ)
    [AddAmenable (A ⧸ φ.ker)] : AddAmenable φ.range :=
  .of_denseRange ⟨QuotientAddGroup.rangeKerLift φ, QuotientAddGroup.continuous_rangeKerLift hφ⟩
    (QuotientAddGroup.rangeKerLift_surjective φ).denseRange

attribute [to_additive existing] Amenable.range_of_quotient_ker

/-- For a strict additive homomorphism `φ : A →+ B`, the quotient `A ⧸ φ.ker` with the quotient
topology is amenable exactly when the range of `φ` with the subspace topology is. -/
theorem addAmenable_quotient_ker_iff_range_of_isStrictMap {φ : A →+ B} (hφ : IsStrictMap φ) :
    AddAmenable (A ⧸ φ.ker) ↔ AddAmenable φ.range :=
  (ContinuousAddEquiv.quotientKerEquivRange hφ).addAmenable_iff

attribute [to_additive existing addAmenable_quotient_ker_iff_range_of_isStrictMap]
  amenable_quotient_ker_iff_range_of_isStrictMap

section DiscreteTopology

variable [DiscreteTopology A]

/-- The range of an additive homomorphism out of an amenable discrete additive group is amenable,
for every additive-group topology on the target. -/
instance AddAmenable.range_of_discreteTopology [AddAmenable A] (φ : A →+ B) :
    AddAmenable φ.range :=
  .of_surjective φ.rangeRestrict φ.rangeRestrict_surjective

attribute [to_additive existing] Amenable.range_of_discreteTopology

/-- For an additive homomorphism `φ` of discrete additive groups, the quotient `A ⧸ φ.ker` is
amenable exactly when the image `φ.range` is. -/
theorem addAmenable_quotient_ker_iff_range [DiscreteTopology B] (φ : A →+ B) :
    AddAmenable (A ⧸ φ.ker) ↔ AddAmenable φ.range := by
  have := QuotientAddGroup.discreteTopology (isOpen_discrete (φ.ker : Set A))
  exact (QuotientAddGroup.quotientKerEquivRange φ).addAmenable_iff_of_discreteTopology

attribute [to_additive existing addAmenable_quotient_ker_iff_range]
  amenable_quotient_ker_iff_range

/-- For a surjective additive homomorphism `φ : A →+ B` of discrete additive groups, the quotient
`A ⧸ φ.ker` is amenable exactly when `B` is. -/
theorem addAmenable_quotient_ker_iff_of_surjective [DiscreteTopology B] {φ : A →+ B}
    (hφ : Function.Surjective φ) : AddAmenable (A ⧸ φ.ker) ↔ AddAmenable B := by
  have := QuotientAddGroup.discreteTopology (isOpen_discrete (φ.ker : Set A))
  exact (QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).addAmenable_iff_of_discreteTopology

attribute [to_additive existing addAmenable_quotient_ker_iff_of_surjective]
  amenable_quotient_ker_iff_of_surjective

end DiscreteTopology

end Additive

end TauCeti
