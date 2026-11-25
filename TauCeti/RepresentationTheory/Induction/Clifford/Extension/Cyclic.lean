/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Splitting
import TauCeti.CategoryTheory.Preadditive.Schur
import TauCeti.GroupTheory.GroupExtension.Cyclic
import TauCeti.GroupTheory.QuotientGroup.KerEquiv
import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Commutant

/-!
# Extending irreducible representations across cyclic quotients

Over an algebraically closed field, an irreducible representation of a normal subgroup with
cyclic quotient extends to its inertia group. In particular, if it is invariant under the
ambient group, it extends to that group, even if the original group extension does not split.

The construction uses the canonical Clifford extension: its kernel consists of scalars by
Schur's lemma. Rescaling a lift of a quotient generator by a root of a scalar makes it satisfy
the generator's order relation.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985),
  for the Clifford obstruction to extension.
-/

public section

open CategoryTheory TauCeti

namespace TauCeti.CliffordExtension

variable {k G : Type*} [Field k] [Group G] {N : Subgroup G} [N.Normal]

/-- The Clifford extension of a simple representation over an algebraically closed field
splits when the inertia quotient is cyclic. -/
theorem nonempty_splitting_of_isCyclic {A : FDRep k N} [IsAlgClosed k] [Simple A]
    [IsCyclic (Quotient A)] : Nonempty (groupExtension A).Splitting := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic (Quotient A))
  let e := (endAlgEquivOfSimple k A).symm
  refine (groupExtension A).nonempty_splitting_of_zpowers_eq_top hg
    (inl_range_le_center_of_surjective_algebraMap (bijective_algebraMap_end_of_simple k A).2) ?_
  intro hm d
  obtain ⟨a, rfl⟩ := (Units.mapEquiv e.toMulEquiv).surjective d
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : k) hm
  have hz₀ : z ≠ 0 := by
    rintro rfl
    exact a.ne_zero (hz.symm.trans (zero_pow hm.ne'))
  refine ⟨Units.mapEquiv e.toMulEquiv (Units.mk0 z hz₀), ?_⟩
  exact ((map_pow (Units.mapEquiv e.toMulEquiv) _ _).symm).trans
    (congrArg (Units.mapEquiv e.toMulEquiv) (Units.ext hz))

end TauCeti.CliffordExtension

namespace FDRep

open TauCeti.CliffordExtension

variable {k G : Type*} [Field k] [Group G] {N : Subgroup G} [N.Normal]

/-- An irreducible representation of a normal subgroup with cyclic ambient quotient extends
on the same carrier to its inertia group over an algebraically closed field. -/
theorem exists_inertiaExtension_of_isCyclic_quotient (A : FDRep k N) [IsAlgClosed k]
    [Simple A] [IsCyclic (G ⧸ N)] :
    ∃ σ : Representation k (inertia A) A,
      σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ := by
  let e := N.quotientSubgroupOfMulEquivMap (inertia A)
  have : IsCyclic (Quotient A) := isCyclic_of_injective
    ((Subgroup.subtype _).comp e.toMonoidHom) (Subtype.coe_injective.comp e.injective)
  exact (nonempty_splitting_iff A).mp nonempty_splitting_of_isCyclic

/-- An invariant irreducible representation of a normal subgroup with cyclic quotient extends
on the same carrier to the ambient group over an algebraically closed field. -/
theorem exists_extension_of_isCyclic_quotient (A : FDRep k N) [IsAlgClosed k] [Simple A]
    [IsCyclic (G ⧸ N)] (hA : inertia A = ⊤) :
    ∃ σ : Representation k G A, σ.comp N.subtype = A.ρ := by
  obtain ⟨τ, hτ⟩ := A.exists_inertiaExtension_of_isCyclic_quotient
  let f := (Subgroup.inclusion hA.ge).comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom
  refine ⟨τ.comp f, ?_⟩
  ext n v
  exact DFunLike.congr_fun (DFunLike.congr_fun hτ n) v

end FDRep
