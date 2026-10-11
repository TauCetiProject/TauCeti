/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.RelationModule.Basic
public import TauCeti.Topology.Algebra.Module.AutomaticContinuity
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Continuous maps from a profinite relation module

Lyndon's isomorphism identifies the abelian pro-`p` quotient of the relation subgroup of a
finite profinite presentation with its algebraic `ℤ_p[G]`-relation module. Every `ℤ_p`-linear
map out of that relation module into a topological `ℤ_p`-module gives a continuous additive
map on the abelian pro-`p` quotient. This permits algebraic relation-module maps to act on the
kernels of profinite group extensions, without installing a second topology on the relation
module.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (5.6.6) and the proof of (7.4.1).
-/

public section

namespace TauCeti.freeProfiniteGroup

open Additive

universe u

variable (p : ℕ) [Fact p.Prime] {G : Type u} [Group G] [Finite G] [TopologicalSpace G]
  [DiscreteTopology G] {ι : Type u} [Fintype ι] [DecidableEq ι] {g : ι → G}
  (hg : Subgroup.closure (Set.range g) = ⊤)

/-- A linear map out of the algebraic relation module, read on the abelian pro-`p` quotient
of the relation subgroup through Lyndon's isomorphism, is continuous. The codomain need not
be finitely generated or Hausdorff. -/
theorem continuous_comp_abelianizationProPEquivRelationModule
    {M : Type*} [AddCommMonoid M] [Module ℤ_[p] M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousSMul ℤ_[p] M]
    (β : MonoidAlgebra.relationModule ℤ_[p] G g →ₗ[ℤ_[p]] M) :
    Continuous (β ∘ abelianizationProPEquivRelationModule p hg) := by
  let R := (lift g : freeProfiniteGroup ι →* G).ker
  have : CompactSpace R :=
    isCompact_iff_compactSpace.mp (isClosed_singleton.preimage (lift g).continuous).isCompact
  let A := abelianizationProP p (freeProfiniteGroup ι) R
  let hA : IsProP p A := isProP_maximalProPQuotient
  let _ := hA.module
  let _ := hA.continuousSMul_module
  -- The local module structure on `Additive A` is p-adic exponentiation; the existing
  -- characteristic equation for Lyndon's isomorphism pins its scalar compatibility.
  let e : Additive A ≃ₗ[ℤ_[p]] MonoidAlgebra.relationModule ℤ_[p] G g :=
    (abelianizationProPEquivRelationModule p hg).toLinearEquiv fun c x ↦ by
      rw [hA.module_smul]
      exact abelianizationProPEquivRelationModule_padicPow p hg x.toMul c
  have : Module.Finite ℤ_[p] (MonoidAlgebra.relationModule ℤ_[p] G g) :=
    Module.Finite.of_injective
      ((MonoidAlgebra.relationModule ℤ_[p] G g).subtype.restrictScalars ℤ_[p])
      Subtype.val_injective
  have : Module.Finite ℤ_[p] (Additive A) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  exact (β.comp e.toLinearMap).continuous_of_finite_of_compactSpace

end TauCeti.freeProfiniteGroup
