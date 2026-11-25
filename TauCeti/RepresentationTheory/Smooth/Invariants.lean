/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.RepresentationTheory.Smooth.Abelian
import TauCeti.RepresentationTheory.Invariants

/-!
# Invariants of smooth representations under subgroups

For a subgroup `U` of a topological group `G`, in practice a compact open subgroup of a locally
profinite group, the `U`-invariants of a representation `V` of `G` are Mathlib's invariants of the
restriction, `V^U = (ρ.comp U.subtype).invariants`. On smooth representations this is the functor
`TauCeti.SmoothRep.invariantsFunctor U : SmoothRep A G ⥤ ModuleCat A`: the inclusion into
`Rep A G`, then restriction to `U`, then Mathlib's `Rep.invariantsFunctor`. It is `A`-linear and
left exact, since the inclusion of the smooth representations preserves kernels and the other two
functors preserve limits.

Invariants may be taken in stages. For a normal subgroup `S` of `G`, the `G`-invariants of `V` are
the `G ⧸ S`-invariants of the representation `Representation.quotientToInvariants ρ S` on `V^S`.
Applied to the restriction to `U`, for `U' ≤ U` with `U'` normal in `U`, this is
`V^U = (V^{U'})^{U/U'}`: the invariants of the restriction of `ρ|_U` to `U'.subgroupOf U` are the
`U'`-invariants of `ρ` (`Representation.invariants_comp_subtype_subgroupOf`).

## Main definitions

* `Representation.quotientToInvariantsInvariantsEquiv`: for a normal subgroup `S`, the
  `G ⧸ S`-invariants of `V^S` are linearly equivalent to `V^G`, by the inclusion.
* `TauCeti.SmoothRep.invariantsFunctor U`: the functor `V ↦ V^U` on smooth representations.

## Main results

* `Representation.map_subtype_invariants_quotientToInvariants`: `(V^S)^{G/S} = V^G` as
  submodules of `V`.
* `Representation.invariants_comp_subtype_subgroupOf`: for `U' ≤ U`, the invariants of `ρ|_U`
  under `U'.subgroupOf U` are the `U'`-invariants of `ρ`.
* `TauCeti.SmoothRep.preservesFiniteLimits_invariantsFunctor`: taking `U`-invariants of smooth
  representations is left exact.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §2.2, Proposition 6(1) and its proof, p. 14.
-/

@[expose] public section

open CategoryTheory Limits

universe w u v

namespace Representation

section Quotient

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- **Invariants in stages.** For a normal subgroup `S`, a vector of `V^S` is invariant under
`G ⧸ S` exactly when it is invariant under `G`: `(V^S)^{G/S} = V^G` as submodules of `V`. -/
theorem map_subtype_invariants_quotientToInvariants (S : Subgroup G) [S.Normal] :
    (ρ.quotientToInvariants S).invariants.map (invariants (ρ.comp S.subtype)).subtype =
      ρ.invariants := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩ g
    exact congrArg Subtype.val (hw (g : G ⧸ S))
  · intro hv
    refine ⟨⟨v, fun s ↦ hv s⟩, fun q ↦ ?_, rfl⟩
    induction q using QuotientGroup.induction_on with
    | H g => exact Subtype.ext (hv g)

/-- For a normal subgroup `S`, the inclusion identifies the `G ⧸ S`-invariants of `V^S` with the
`G`-invariants of `V`. -/
noncomputable def quotientToInvariantsInvariantsEquiv (S : Subgroup G) [S.Normal] :
    (ρ.quotientToInvariants S).invariants ≃ₗ[k] ρ.invariants :=
  (Submodule.equivMapOfInjective _ (invariants (ρ.comp S.subtype)).injective_subtype _).trans
    (LinearEquiv.ofEq _ _ (map_subtype_invariants_quotientToInvariants ρ S))

@[simp]
theorem coe_quotientToInvariantsInvariantsEquiv_apply (S : Subgroup G) [S.Normal]
    (v : (ρ.quotientToInvariants S).invariants) :
    (ρ.quotientToInvariantsInvariantsEquiv S v : V) = v :=
  rfl

/-- For subgroups `U' ≤ U`, the invariants of the restriction `ρ|_U` under `U'`, viewed as the
subgroup `U'.subgroupOf U` of `U`, are the `U'`-invariants of `ρ`. Together with
`map_subtype_invariants_quotientToInvariants` applied to `ρ|_U`, this gives
`V^U = (V^{U'})^{U/U'}` when `U'` is normal in `U`. -/
theorem invariants_comp_subtype_subgroupOf {U U' : Subgroup G} (h : U' ≤ U) :
    invariants ((ρ.comp U.subtype).comp (U'.subgroupOf U).subtype) =
      invariants (ρ.comp U'.subtype) := by
  rw [invariants_comp_comp_subtype, Subgroup.subgroupOf_map_subtype, inf_of_le_left h]

end Quotient

end Representation

namespace TauCeti

namespace SmoothRep

variable (A : Type u) [CommRing A] {G : Type v} [Group G] [TopologicalSpace G]

/-- The functor `V ↦ V^U` of `U`-invariants on smooth representations, for a subgroup `U` of `G`
(in practice compact open): the inclusion into `Rep A G`, then restriction to `U`, then Mathlib's
`Rep.invariantsFunctor`. Morphisms act by restriction. -/
noncomputable abbrev invariantsFunctor (U : Subgroup G) : SmoothRep.{w} A G ⥤ ModuleCat.{w} A :=
  ι A G ⋙ Rep.resFunctor U.subtype ⋙ Rep.invariantsFunctor A U

variable {A}

/-- **Invariants are left exact.** The inclusion `SmoothRep A G ⥤ Rep A G` preserves kernels,
hence finite limits, while restriction preserves limits and Mathlib's invariants functor is a
right adjoint. -/
instance preservesFiniteLimits_invariantsFunctor [SeparatelyContinuousMul G] (U : Subgroup G) :
    PreservesFiniteLimits (invariantsFunctor.{w} A U) :=
  haveI : PreservesFiniteLimits (ι.{w} A G) := Functor.preservesFiniteLimits_of_preservesKernels _
  inferInstance

end SmoothRep

end TauCeti
