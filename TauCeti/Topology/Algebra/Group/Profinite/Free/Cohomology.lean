/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Cohomology
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Extension

/-!
# `H²` of a free pro-`p` group vanishes

Let `F = freeProP p X` be the free pro-`p` group on a type `X`. It is projective
(`TauCeti.isProjective_of_hasPGroupSolutions` at `TauCeti.hasPGroupSolutions_freeProP`), so every
extension `1 → M → E → F → 1` of topological groups with profinite total group `E` and pro-`p`
kernel `M` splits by a continuous homomorphic section
(`GroupExtension.exists_splitting_continuous_of_isProjective`).

Read through the classification of profinite extensions by continuous `H²`, this is the vanishing of
the second continuous cohomology of a free pro-`p` group with coefficients in any profinite pro-`p`
abelian `F`-module `M`: every class of the explicit `H²(F, M)` is the class of a profinite extension
of `F` by `M`, and the class of a split extension is zero. That vanishing is
`TauCeti.IsProjective.subsingleton_H2` applied to the projectivity of `F`, and this file records
its consequences in the forms the free pro-`p` theory consumes: for a `p`-primary torsion module
written additively (`TauCeti.freeProP.subsingleton_H2_of_isPPrimaryTorsion`), in particular for
`𝔽_p` with any continuous action (`TauCeti.freeProP.subsingleton_H2_zmod`), and, transported
through the degree-two comparison with Mathlib's `continuousCohomology`, for a finite discrete
`p`-primary `F`-module (`TauCeti.freeProP.subsingleton_continuousCohomology_two`, with the additive
form `TauCeti.freeProP.subsingleton_continuousCohomology_two_of_isPPrimaryTorsion`).

No finiteness of `X` is needed: the universal property of `freeProP p X` holds for every type, and
the argument uses nothing else about `F`.

## Main results

* `TauCeti.freeProP.subsingleton_H2_of_isPPrimaryTorsion`: **`H²(F, M) = 0`** for `F` free pro-`p`
  and `M` a profinite `p`-primary torsion abelian `F`-module written additively, and
  `TauCeti.freeProP.subsingleton_H2_zmod` for `𝔽_p` with any continuous action.
* `TauCeti.freeProP.subsingleton_continuousCohomology_two`: the same in Mathlib's
  `continuousCohomology`, for a finite discrete `p`-primary `F`-module, and
  `TauCeti.freeProP.subsingleton_continuousCohomology_two_of_isPPrimaryTorsion` for such a module
  written additively.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.4.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III, §5.
-/

public section

namespace TauCeti

universe u v

open ContCohomology

variable {p : ℕ} {X : Type u}

namespace freeProP

/-! ### The vanishing of `H²` -/

section Additive

variable {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [CompactSpace M] [TotallyDisconnectedSpace M] [DistribMulAction (freeProP p X) M]
  [ContinuousSMul (freeProP p X) M]

/-- **`H²` of a free pro-`p` group vanishes, additive form.** For `F = freeProP p X` and `M` a
profinite `p`-primary torsion abelian group, written additively, with a continuous action of `F`,
the explicit second continuous cohomology group `H²(F, M)` is zero. -/
theorem subsingleton_H2_of_isPPrimaryTorsion (hM : IsPPrimaryTorsion p M) :
    Subsingleton (H2 (freeProP p X) M) :=
  IsProjective.subsingleton_H2_of_isPPrimaryTorsion
    (isProjective_of_hasPGroupSolutions (hasPGroupSolutions_freeProP p X)) (isProP_freeProP p X) hM

/-- **`H²(F, 𝔽_p) = 0` for a free pro-`p` group `F`**, for every continuous action of `F` on
`𝔽_p`. -/
theorem subsingleton_H2_zmod [NeZero p] [DistribMulAction (freeProP p X) (ZMod p)]
    [ContinuousSMul (freeProP p X) (ZMod p)] : Subsingleton (H2 (freeProP p X) (ZMod p)) :=
  subsingleton_H2_of_isPPrimaryTorsion (isPPrimaryTorsion_iff.2 fun m ↦
    ⟨1, by rw [pow_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]⟩)

end Additive

section Discrete

variable {M : Type u} [CommGroup M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
  [MulDistribMulAction (freeProP p X) M] [ContinuousSMul (freeProP p X) M]

/-- **`H²` of a free pro-`p` group vanishes**, in Mathlib's continuous cohomology: for a finite
discrete `p`-primary abelian group `M` with a continuous action of `F = freeProP p X`, the canonical
`continuousCohomology 2` of the topological representation attached to `M` is zero. -/
theorem subsingleton_continuousCohomology_two (hM : IsPGroup p M) :
    Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ (freeProP p X) (Additive M))) :=
  haveI := (isProjective_of_hasPGroupSolutions (hasPGroupSolutions_freeProP p X)).subsingleton_H2
    (isProP_freeProP p X) hM.isProP
  (explicitH2AddEquivContinuousCohomology (freeProP p X) (Additive M)).toEquiv.symm.subsingleton

end Discrete

/-- **`H²` of a free pro-`p` group vanishes on finite additive coefficients**, in Mathlib's
continuous cohomology: for a finite discrete `p`-primary torsion abelian group `M`, written
additively, with a continuous action of `F = freeProP p X`, the canonical `continuousCohomology 2`
of the topological representation attached to `M` is zero. -/
theorem subsingleton_continuousCohomology_two_of_isPPrimaryTorsion (M : Type u) [AddCommGroup M]
    [TopologicalSpace M] [DiscreteTopology M] [Finite M] [DistribMulAction (freeProP p X) M]
    [ContinuousSMul (freeProP p X) M] (hM : IsPPrimaryTorsion p M) :
    Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ (freeProP p X) M)) :=
  haveI := subsingleton_H2_of_isPPrimaryTorsion (X := X) hM
  (explicitH2AddEquivContinuousCohomology (freeProP p X) M).toEquiv.symm.subsingleton

end freeProP

end TauCeti
