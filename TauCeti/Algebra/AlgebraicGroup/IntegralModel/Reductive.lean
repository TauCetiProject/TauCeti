/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.IntegralModel.Basic
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Over

/-!
# Reductive models and hyperspecial subgroups

Let `O` be a local ring with residue field `κ`, with an algebra map to a field `K`, and let `𝒢`
be a smooth affine `O`-model of an affine `K`-group `G`. The model is reductive when its two
selected base changes, the generic fiber `G` over `K` and the special fiber over `κ`, are
connected reductive groups. When `O` is a discrete valuation ring with fraction field `K`, these
are the generic and special fibers of `Spec O[𝒢] → Spec O`. For general `O` other fibers are not
tested, so this is weaker than asking `O[𝒢]` to be a reductive group scheme over `O` in the sense
of `TauCeti.reductiveCommHopfAlgPropertyOver`, whose every geometric fiber is connected reductive;
such a group scheme gives a reductive model.

The predicate `IsHyperspecialSubgroup O P` says that a subgroup `P` of `G(K)` is the group of
integral points of some reductive model over `O`. It is a generalization, to an arbitrary local
ring `O` with an algebra map to `K`, of the hyperspecial subgroups of a reductive group over a
local field `K` with valuation ring `O`.

## Main declarations

* `TauCeti.IntegralModel.SmoothModel.IsReductive`: the condition on the two selected base changes.
* `TauCeti.IntegralModel.SmoothModel.isReductive_of_reductiveCommHopfAlgPropertyOver`: a reductive
  group scheme over `O` gives a reductive model.
* `TauCeti.IntegralModel.IsHyperspecialSubgroup`: the integral points of some reductive model.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local II*, Publ. Math. IHÉS 60 (1984),
  4.6.31, pp. 136–137.
* J. Tits, *Reductive groups over local fields*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 1 (1979), §3.8.1.
* B. Conrad, *Reductive group schemes* (2014), Definition 3.1.1.
-/

public section

namespace TauCeti.IntegralModel

universe u

variable {O K : Type u} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K]

namespace SmoothModel

variable {H : FiniteTypeCommHopfAlgCat.{u, u} K} (𝒢 : SmoothModel O K H)

/-- A smooth model is reductive when its two selected base changes, the generic fiber `G` over `K`
and the special fiber over the residue field of `O`, are connected reductive groups. When `O` is a
discrete valuation ring with fraction field `K` these are its generic and special fibers
([Bruhat–Tits II], 4.6.31). For general `O` this tests only these two base changes, unlike
[Conrad], Definition 3.1.1, which asks every geometric fiber to be connected reductive. -/
def IsReductive : Prop :=
  reductiveCommHopfAlgProperty K H ∧
    reductiveCommHopfAlgProperty (IsLocalRing.ResidueField O) 𝒢.specialFiber

/-- Unfolding lemma for `SmoothModel.IsReductive`. -/
theorem isReductive_iff :
    𝒢.IsReductive ↔ reductiveCommHopfAlgProperty K H ∧
      reductiveCommHopfAlgProperty (IsLocalRing.ResidueField O) 𝒢.specialFiber :=
  Iff.rfl

variable {𝒢}

/-- The generic fiber of a reductive model is a connected reductive group. -/
theorem IsReductive.genericFiber (h𝒢 : 𝒢.IsReductive) : reductiveCommHopfAlgProperty K H :=
  h𝒢.1

/-- The special fiber of a reductive model is a connected reductive group. -/
theorem IsReductive.specialFiber (h𝒢 : 𝒢.IsReductive) :
    reductiveCommHopfAlgProperty (IsLocalRing.ResidueField O) 𝒢.specialFiber :=
  h𝒢.2

/-- A reductive model has connected fibers. -/
theorem IsReductive.hasConnectedFibers (h𝒢 : 𝒢.IsReductive) : 𝒢.HasConnectedFibers :=
  (hasConnectedFibers_iff 𝒢).2 ⟨h𝒢.1.geometricallyConnected, h𝒢.2.geometricallyConnected⟩

/-- A smooth model whose coordinate algebra is a reductive group scheme over `O` is a reductive
model. -/
theorem isReductive_of_reductiveCommHopfAlgPropertyOver
    (h𝒢 : reductiveCommHopfAlgPropertyOver O 𝒢.coord) : 𝒢.IsReductive :=
  ⟨(reductiveCommHopfAlgProperty K).prop_of_iso 𝒢.genericFiberIso (h𝒢.fiber K),
    h𝒢.fiber (IsLocalRing.ResidueField O)⟩

end SmoothModel

variable (O) in
/-- A subgroup `P` of `G(K)` is hyperspecial over the local ring `O` when it is the group of
integral points of a reductive model of `G` over `O`. This generalizes to an arbitrary local ring
`O` with an algebra map to `K` the hyperspecial subgroups of a reductive group over a local field
`K` with valuation ring `O` ([Tits], §3.8.1). -/
def IsHyperspecialSubgroup {H : FiniteTypeCommHopfAlgCat.{u, u} K}
    (P : Subgroup (WithConv (H →ₐ[K] K))) : Prop :=
  ∃ 𝒢 : SmoothModel O K H, 𝒢.IsReductive ∧ 𝒢.integralPoints = P

variable (O) in
/-- Unfolding lemma for `IsHyperspecialSubgroup`. -/
theorem isHyperspecialSubgroup_iff {H : FiniteTypeCommHopfAlgCat.{u, u} K}
    (P : Subgroup (WithConv (H →ₐ[K] K))) :
    IsHyperspecialSubgroup O P ↔ ∃ 𝒢 : SmoothModel O K H, 𝒢.IsReductive ∧ 𝒢.integralPoints = P :=
  Iff.rfl

/-- The integral points of a reductive model satisfy `IsHyperspecialSubgroup`. -/
theorem SmoothModel.IsReductive.isHyperspecialSubgroup {H : FiniteTypeCommHopfAlgCat.{u, u} K}
    {𝒢 : SmoothModel O K H} (h𝒢 : 𝒢.IsReductive) :
    IsHyperspecialSubgroup O 𝒢.integralPoints :=
  ⟨𝒢, h𝒢, rfl⟩

end TauCeti.IntegralModel
