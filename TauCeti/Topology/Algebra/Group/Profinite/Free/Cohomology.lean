/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Torsion
public import TauCeti.Topology.Algebra.GroupAction.TypeTags
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Extension
public import TauCeti.Topology.Algebra.GroupExtension.Cohomology

/-!
# `H²` of a free pro-`p` group vanishes

Let `F = freeProP p X` be the free pro-`p` group on a type `X`. Every extension `1 → M → E → F → 1`
of topological groups with profinite total group `E` and pro-`p` kernel `M` splits by a continuous
homomorphic section (`GroupExtension.exists_splitting_continuous_freeProP`, in
`TauCeti.Topology.Algebra.Group.Profinite.Free.Extension`).

Read through the classification of profinite extensions by continuous `H²`, this is the vanishing of
the second continuous cohomology of a free pro-`p` group with coefficients in any profinite pro-`p`
abelian `F`-module `M` (`TauCeti.freeProP.subsingleton_H2`): every class of the explicit
`H²(F, M)` is the class of a profinite extension of `F` by `M`, and the class of a split extension
is zero. Transported through the degree-two comparison with Mathlib's `continuousCohomology`, the
statement takes its canonical form for a finite discrete `p`-primary `F`-module
(`TauCeti.freeProP.subsingleton_continuousCohomology_two`).

No finiteness of `X` is needed: the universal property of `freeProP p X` holds for every type, and
the argument uses nothing else about `F`. The extension dictionary reads its abelian kernel
multiplicatively, so the vanishing is first stated for a `CommGroup` `M`; an `AddCommGroup` `M` is
`Additive (Multiplicative M)`, and `TauCeti.freeProP.subsingleton_H2_of_isPPrimaryTorsion` restates
the vanishing for it, which is the form the `𝔽_p`-valued theory consumes.

## Main results

* `TauCeti.freeProP.subsingleton_H2`: **`H²(F, M) = 0`** for `F` free pro-`p` and `M` a profinite
  pro-`p` abelian `F`-module.
* `TauCeti.freeProP.subsingleton_H2_of_isPPrimaryTorsion`: the same for a profinite `p`-primary
  torsion abelian `F`-module written additively, and `TauCeti.freeProP.subsingleton_H2_zmod` for
  `𝔽_p` with any continuous action.
* `TauCeti.freeProP.subsingleton_continuousCohomology_two`: the same in Mathlib's
  `continuousCohomology`, for a finite discrete `p`-primary `F`-module.

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

section Cohomology

variable {M : Type v} [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [CompactSpace M]
  [TotallyDisconnectedSpace M] [MulDistribMulAction (freeProP p X) M]
  [ContinuousSMul (freeProP p X) M]

/-- **`H²` of a free pro-`p` group vanishes.** For `F = freeProP p X` and `M` a profinite pro-`p`
abelian group with a continuous action of `F`, the explicit second continuous cohomology group
`H²(F, M)` is zero. -/
theorem subsingleton_H2 (hM : IsProP p M) : Subsingleton (H2 (freeProP p X) (Additive M)) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨Y, rfl⟩ := ProfiniteGroupExtension.exists_contCohomologyClass_eq c
  rw [ProfiniteGroupExtension.contCohomologyClass_def,
    ← Y.toGroupExtension.exists_splitting_continuous_iff_contCohomologyClass_eq_zero]
  exact Y.toGroupExtension.exists_splitting_continuous_freeProP Y.continuous_inl
    Y.continuous_rightHom hM

end Cohomology

section Additive

variable {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [CompactSpace M] [TotallyDisconnectedSpace M] [DistribMulAction (freeProP p X) M]
  [ContinuousSMul (freeProP p X) M]

/-- **`H²` of a free pro-`p` group vanishes, additive form.** For `F = freeProP p X` and `M` a
profinite `p`-primary torsion abelian group, written additively, with a continuous action of `F`,
the explicit second continuous cohomology group `H²(F, M)` is zero. -/
theorem subsingleton_H2_of_isPPrimaryTorsion (hM : IsPPrimaryTorsion p M) :
    Subsingleton (H2 (freeProP p X) M) :=
  -- `Additive (Multiplicative M)` is `M` with the same instances, so the multiplicative statement
  -- applies as it stands; `isPPrimaryTorsion_additive_iff` reads the hypothesis the same way.
  subsingleton_H2 (X := X) (M := Multiplicative M)
    (IsPGroup.isProP ((isPPrimaryTorsion_additive_iff (M := Multiplicative M)).1 hM))

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
  haveI := subsingleton_H2 (X := X) hM.isProP
  (explicitH2AddEquivContinuousCohomology (freeProP p X) (Additive M)).toEquiv.symm.subsingleton

end Discrete

end freeProP

end TauCeti
