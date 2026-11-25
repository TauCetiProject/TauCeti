/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
public import Mathlib.Topology.Maps.Strict.Group

import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The topological first isomorphism theorem

A surjective strict homomorphism of topological groups `f : G →* H` induces an isomorphism of
topological groups `G ⧸ f.ker ≃ₜ* H`: the kernel lift of a strict homomorphism is an embedding
(Mathlib's `MonoidHom.isStrictMap_iff_isEmbedding_kerLift`), and a surjective embedding is a
homeomorphism. This is Mathlib's `ContinuousMulEquiv.quotientKerEquivRange` with the range
replaced by the whole target.

A continuous surjection from a compact group to a Hausdorff group is a closed map, hence strict,
so it is a special case; that case permits changing the quotient model in profinite extensions.

A continuous open homomorphism is strict, and its range is an open, hence closed, subgroup of the
target. So the quotient of its source by its kernel is compact when the target is.

## Main definitions

* `ContinuousMulEquiv.quotientKerEquivOfSurjective` and
  `ContinuousAddEquiv.quotientKerEquivOfSurjective`: the isomorphism `G ⧸ f.ker ≃ₜ* H` induced by
  a surjective strict homomorphism `f`, with the evaluation lemmas
  `quotientKerEquivOfSurjective_apply_mk` and `quotientKerEquivOfSurjective_symm_apply`.
* `ContinuousMonoidHom.quotientKerEquivOfSurjective`: the case of a continuous surjection from a
  compact group to a Hausdorff group.
* `MonoidHom.compactSpace_quotient_ker_of_isOpenMap` and
  `AddMonoidHom.compactSpace_quotient_ker_of_isOpenMap`: the quotient by the kernel of a continuous
  open homomorphism is compact when the target is.

## Main statements

* `TauCeti.QuotientGroup.continuous_rangeKerLift` and
  `TauCeti.QuotientAddGroup.continuous_rangeKerLift`: the kernel lift `G ⧸ f.ker →* f.range` of a
  continuous homomorphism is continuous, for the quotient topology on the source and the subspace
  topology on the range.

## References

* N. Bourbaki, *General Topology*, Chapters 1–4, Springer (1989), Chapter III (Topological
  groups), § 2 (Subgroups, quotient groups, homomorphisms of topological groups).
-/

public section

namespace ContinuousMulEquiv

open Topology

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  (f : G →* H)

/-- **The first isomorphism theorem for a surjective strict homomorphism** of topological groups:
`G ⧸ f.ker ≃ₜ* H`. -/
@[to_additive /-- **The first isomorphism theorem for a surjective strict homomorphism** of
topological additive groups: `G ⧸ f.ker ≃ₜ+ H`. -/]
noncomputable def quotientKerEquivOfSurjective (hf : IsStrictMap f) (hs : Function.Surjective f) :
    G ⧸ f.ker ≃ₜ* H :=
  -- The kernel lift of a strict homomorphism is an embedding, and it is surjective because `f` is.
  let h : G ⧸ f.ker ≃ₜ H :=
    (MonoidHom.isStrictMap_iff_isEmbedding_kerLift.mp hf).toHomeomorphOfSurjective
      (Function.Surjective.of_comp (g := QuotientGroup.mk) hs)
  { h with
    map_mul' := fun x y => by
      simp only [h, Equiv.toFun_as_coe, Homeomorph.coe_toEquiv,
        IsEmbedding.toHomeomorphOfSurjective_apply, map_mul] }

/-- The quotient isomorphism evaluates on the class of `x` as `f x`. -/
@[to_additive (attr := simp) /-- The quotient isomorphism evaluates on the class of `x` as
`f x`. -/]
theorem quotientKerEquivOfSurjective_apply_mk (hf : IsStrictMap f) (hs : Function.Surjective f)
    (x : G) : quotientKerEquivOfSurjective f hf hs (x : G ⧸ f.ker) = f x := by
  rw [quotientKerEquivOfSurjective]
  simp only [coe_mk, MulEquiv.coe_mk, Homeomorph.coe_toEquiv,
    IsEmbedding.toHomeomorphOfSurjective_apply, QuotientGroup.kerLift_mk]

/-- The inverse of the quotient isomorphism sends `f x` to the class of `x`. -/
@[to_additive (attr := simp) /-- The inverse of the quotient isomorphism sends `f x` to the class
of `x`. -/]
theorem quotientKerEquivOfSurjective_symm_apply (hf : IsStrictMap f) (hs : Function.Surjective f)
    (x : G) : (quotientKerEquivOfSurjective f hf hs).symm (f x) = (x : G ⧸ f.ker) := by
  rw [← quotientKerEquivOfSurjective_apply_mk f hf hs x, symm_apply_apply]

end ContinuousMulEquiv

namespace ContinuousMonoidHom

variable {G H : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
  [Group H] [TopologicalSpace H] [T2Space H]
  (f : G →ₜ* H) (hf : Function.Surjective f)

/-- The first isomorphism theorem for a continuous surjection from a compact group to a
Hausdorff group, with the quotient topology on the source. -/
noncomputable def quotientKerEquivOfSurjective : (G ⧸ (f : G →* H).ker) ≃ₜ* H :=
  -- A continuous map from a compact space to a Hausdorff space is closed, hence strict.
  ContinuousMulEquiv.quotientKerEquivOfSurjective (f : G →* H)
    (f.continuous.isClosedMap.isStrictMap f.continuous) hf

/-- The topological first isomorphism theorem sends the class of `x` to `f x`. -/
@[simp]
theorem quotientKerEquivOfSurjective_apply_mk (x : G) :
    f.quotientKerEquivOfSurjective hf (QuotientGroup.mk x) = f x := by
  rw [quotientKerEquivOfSurjective, ContinuousMulEquiv.quotientKerEquivOfSurjective_apply_mk,
    MonoidHom.coe_ofClass]

/-- The inverse of the topological first isomorphism theorem sends `f x` to the class of `x`. -/
@[simp]
theorem quotientKerEquivOfSurjective_symm_apply (x : G) :
    (f.quotientKerEquivOfSurjective hf).symm (f x) = QuotientGroup.mk x := by
  rw [quotientKerEquivOfSurjective]
  simpa only [MonoidHom.coe_ofClass] using
    ContinuousMulEquiv.quotientKerEquivOfSurjective_symm_apply (f : G →* H)
      (f.continuous.isClosedMap.isStrictMap f.continuous) hf x

end ContinuousMonoidHom

namespace MonoidHom

variable {G K : Type*} [Group G] [TopologicalSpace G] [Group K] [TopologicalSpace K]

/-- The quotient of the source of a continuous open homomorphism to a compact group by its kernel is
compact. -/
@[to_additive /-- The quotient of the source of a continuous open additive homomorphism to a compact
additive group by its kernel is compact. -/]
theorem compactSpace_quotient_ker_of_isOpenMap [SeparatelyContinuousMul K] [CompactSpace K]
    (f : G →* K) (hc : Continuous f) (ho : IsOpenMap f) : CompactSpace (G ⧸ f.ker) := by
  -- The quotient is the range, an open and hence closed subgroup of `K`.
  have : CompactSpace f.range :=
    isCompact_iff_compactSpace.mp (f.range.isClosed_of_isOpen ho.isOpen_range).isCompact
  exact (ContinuousMulEquiv.quotientKerEquivRange (ho.isStrictMap hc)).symm.toHomeomorph
    |>.compactSpace

end MonoidHom

namespace TauCeti.QuotientGroup

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

/-- The kernel lift `G ⧸ f.ker →* f.range` of a continuous homomorphism `f` is continuous, for the
quotient topology on the source and the subspace topology on the range. -/
@[to_additive TauCeti.QuotientAddGroup.continuous_rangeKerLift
  /-- The kernel lift `G ⧸ f.ker →+ f.range` of a continuous additive homomorphism `f` is
  continuous, for the quotient topology on the source and the subspace topology on the range. -/]
theorem continuous_rangeKerLift {f : G →* H} (hf : Continuous f) :
    Continuous (QuotientGroup.rangeKerLift f) :=
  (QuotientGroup.isQuotientMap_mk f.ker).continuous_iff.2 (hf.subtype_mk _)

end TauCeti.QuotientGroup
