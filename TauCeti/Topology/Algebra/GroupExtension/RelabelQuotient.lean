/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.GroupExtension.Profinite

/-!
# Relabelling the quotient of a profinite extension

A continuous multiplicative equivalence of quotient groups transports a profinite extension
without changing its total group or kernel. The action on the kernel must transport along the
same equivalence. This lets extensions initially over different models of a finite quotient
be compared over the identity of a single group.
-/

public section

namespace TauCeti.ProfiniteGroupExtension

universe u v

variable {G H : Type u} {M : Type v}
  [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [CommGroup M] [TopologicalSpace M] [MulDistribMulAction G M] [MulDistribMulAction H M]
  (X : ProfiniteGroupExtension G M) (e : G ≃ₜ* H)
  (hsmul : ∀ (g : G) (m : M), e g • m = g • m)

/-- Relabel the quotient of a profinite extension, retaining its total group and kernel.
The prescribed actions on the kernel must agree through the quotient equivalence. -/
abbrev relabelQuotient : ProfiniteGroupExtension H M where
  E := X.E
  toGroupExtension := X.toGroupExtension.relabelQuotient e.toMulEquiv
  continuous_inl := by simpa using X.continuous_inl
  continuous_rightHom := by
    simpa using e.continuous.comp X.continuous_rightHom
  inducesAction := X.inducesAction.relabelQuotient e.toMulEquiv hsmul

/-- The underlying exact sequence is obtained by relabelling the quotient. -/
@[simp]
theorem relabelQuotient_toGroupExtension :
    (X.relabelQuotient e hsmul).toGroupExtension =
      X.toGroupExtension.relabelQuotient e.toMulEquiv :=
  (rfl)

end TauCeti.ProfiniteGroupExtension
