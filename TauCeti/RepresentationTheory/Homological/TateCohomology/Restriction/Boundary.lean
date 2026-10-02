/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.AllDegrees
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Connecting.LowDegree

/-!
# Restriction across the boundary of the Tate complex

Restriction commutes with the connecting map from degree `-1` to degree zero. These degrees
straddle the norm differential joining chains to cochains: restriction acts by relative transfer
on the norm kernel and by inclusion on the invariants. Their compatibility follows from
`N_H ∘ relTransfer = N_G` and the norm description of the connecting map.

This is the boundary case needed to dimension-shift the restriction law for cups with a
negative-degree factor.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5.
* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6.
-/

public noncomputable section

universe u

open CategoryTheory Rep

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

attribute [local instance] Subgroup.fintypeOfFinite Subgroup.fintypeQuotientOfFiniteIndex

/-- Tate restriction commutes with the connecting map from degree `-1` to degree zero. -/
@[reassoc (attr := simp)]
theorem δ_comp_res_neg_one {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (H : Subgroup G) :
    _root_.TateCohomology.δ hS (-1) ≫ H0Res S.X₁ H =
      HNegOneRes S.X₃ H ≫ _root_.TateCohomology.δ ((shortExact_res H.subtype).mpr hS) (-1) := by
  ext z
  induction z using HNegOne_induction_on with
  | h z =>
    obtain ⟨y, x, hy, hx, hδ⟩ := exists_δ_neg_one_eq_H0π hS z
    simp only [ConcreteCategory.comp_apply, hδ,
      HNegOneπ_comp_HNegOneRes_apply]
    refine (ConcreteCategory.congr_hom (H0π_comp_H0Res S.X₁ H) x).trans ?_
    apply (δ_neg_one_HNegOneπ ((shortExact_res H.subtype).mpr hS)
      (Representation.relTransferKerNorm S.X₃.ρ H z)
      (Representation.relTransfer S.X₂.ρ H y) ?_
      (Submodule.inclusion (Representation.invariants_le_invariants_comp_subtype
        (ρ := S.X₁.ρ) (H := H)) x) ?_).symm
    · -- Restricting the short complex preserves the underlying coefficient maps. Spell out
      -- that identification so the equivariance lemma can match `S.g`.
      change S.g.hom (Representation.relTransfer S.X₂.ρ H y) =
        (Representation.relTransferKerNorm S.X₃.ρ H z : S.X₃)
      -- The relative transfer is a sum of actions, so it commutes with the coefficient map.
      simp only [Representation.coe_relTransferKerNorm, Representation.relTransfer_apply,
        map_sum]
      exact Finset.sum_congr rfl fun q _ =>
        (Rep.hom_comm_apply S.g q.out⁻¹ y).trans (congrArg (S.X₃.ρ q.out⁻¹) hy)
    · -- The restricted coefficient module has action `ρ.comp H.subtype`; its invariant
      -- inclusion is the identity on underlying elements.
      change S.f.hom x = Representation.norm (S.X₂.ρ.comp H.subtype)
        (Representation.relTransfer S.X₂.ρ H y)
      rwa [Representation.norm_relTransfer_apply]

end TauCeti.TateCohomology
