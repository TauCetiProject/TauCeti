/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.GroupExtension.Profinite

/-!
# Relabelling profinite group extensions

An extension is unchanged when its kernel and quotient are replaced by continuously isomorphic
groups, provided the two prescribed actions correspond. This file packages that transport for
`ProfiniteGroupExtension`, retaining the same profinite total group.

The construction is useful when a quotient presented by a free profinite group and a Galois group
are canonically isomorphic but not definitionally the same type.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  §VII.4, (7.4.1): the relabelling of extensions used to compare a presentation extension with an
  arithmetic one.

-/

public section

namespace TauCeti.ProfiniteGroupExtension

universe u v

variable {G : Type u} {M : Type v} [Group G] [TopologicalSpace G]
  [CommGroup M] [TopologicalSpace M] [MulDistribMulAction G M]

/-- Relabel the kernel and quotient of a profinite extension along continuous multiplicative
equivalences which identify the prescribed actions. The total group is unchanged. Like
`relabelQuotient`, this is an abbreviation so that the relabelled total group and its instances are
reducibly those of `X.E`: `relabel_toGroupExtension` needs this to typecheck, and `simp` needs it
to identify the relabelled inclusion and projection with their original-group forms. -/
abbrev relabel (X : ProfiniteGroupExtension G M)
    {G' : Type u} {M' : Type v} [Group G'] [TopologicalSpace G']
    [CommGroup M'] [TopologicalSpace M'] [MulDistribMulAction G' M']
    (eG : G ≃ₜ* G') (eM : M' ≃ₜ* M)
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m) :
    ProfiniteGroupExtension G' M' where
  E := X.E
  toGroupExtension := _root_.GroupExtension.relabel X.toGroupExtension
    eM.toMulEquiv eG.toMulEquiv
  continuous_inl := by
    rw [GroupExtension.relabel_inl]
    exact X.continuous_inl.comp eM.continuous
  continuous_rightHom := by
    rw [GroupExtension.relabel_rightHom]
    exact eG.continuous.comp X.continuous_rightHom
  inducesAction := X.inducesAction.relabel eM.toMulEquiv eG.toMulEquiv hsmul

/-- The underlying exact sequence is obtained by relabelling both terms of the original one. -/
@[simp]
theorem relabel_toGroupExtension (X : ProfiniteGroupExtension G M)
    {G' : Type u} {M' : Type v} [Group G'] [TopologicalSpace G']
    [CommGroup M'] [TopologicalSpace M'] [MulDistribMulAction G' M']
    (eG : G ≃ₜ* G') (eM : M' ≃ₜ* M)
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m) :
    (X.relabel eG eM hsmul).toGroupExtension =
      X.toGroupExtension.relabel eM.toMulEquiv eG.toMulEquiv :=
  (rfl)

end TauCeti.ProfiniteGroupExtension
