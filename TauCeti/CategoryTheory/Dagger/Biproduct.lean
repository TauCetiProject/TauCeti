/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct
public import TauCeti.CategoryTheory.Dagger.Functor

/-!
# Orthogonal sums in dagger categories

A bicone `c` of a family `F` of objects of a dagger category is *orthogonal* when each inclusion
`c.ι j` is the dagger of the corresponding projection `c.π j`. Its inclusions are then
isometries with mutually orthogonal ranges. An orthogonal limit bicone is an *orthogonal sum*
(also called a *dagger biproduct*) of `F`: unlike a native biproduct, it is determined up to a
unitary isomorphism, not merely up to an isomorphism.

## Main declarations

* `CategoryTheory.Limits.Bicone.IsOrthogonal`: the inclusions of a bicone are the daggers of its
  projections.
* `CategoryTheory.Limits.Bicone.IsOrthogonal.map`: dagger functors preserve orthogonal bicones.
* `CategoryTheory.Limits.Bicone.IsOrthogonal.isUnitary_conePointUniqueUpToIso_hom`: the
  comparison isomorphism between the points of two orthogonal limit bicones of the same family is
  unitary.
* `TauCeti.HasOrthogonalBiproduct`: a family has an orthogonal sum, with a chosen orthogonal limit
  bicone `TauCeti.HasOrthogonalBiproduct.limitBicone`.
* `TauCeti.HasFiniteOrthogonalBiproducts`: every finite family has an orthogonal sum.

## References

* P. Selinger, *Dagger compact closed categories and completely positive maps*, Electron. Notes
  Theor. Comput. Sci. 170 (2007), 139–163.
* C. Heunen, J. Vicary, *Categories for Quantum Theory*, Oxford University Press, 2019.
-/

public section

open CategoryTheory Limits TauCeti

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits.Bicone

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [DaggerCategory C]
variable {J : Type w} {F : J → C}

/-- A bicone in a dagger category is *orthogonal* when each inclusion is the dagger of the
corresponding projection. -/
def IsOrthogonal (c : Bicone F) : Prop :=
  ∀ j, dagger (c.π j) = c.ι j

/-- A bicone is orthogonal exactly when the dagger of each projection is the corresponding
inclusion. -/
theorem isOrthogonal_iff (c : Bicone F) : c.IsOrthogonal ↔ ∀ j, dagger (c.π j) = c.ι j :=
  Iff.rfl

namespace IsOrthogonal

variable {c : Bicone F}

/-- The dagger of a projection of an orthogonal bicone is the corresponding inclusion. -/
theorem dagger_π (hc : c.IsOrthogonal) (j : J) : dagger (c.π j) = c.ι j :=
  hc j

/-- The dagger of an inclusion of an orthogonal bicone is the corresponding projection. -/
theorem dagger_ι (hc : c.IsOrthogonal) (j : J) : dagger (c.ι j) = c.π j := by
  rw [← hc.dagger_π, dagger_dagger]

/-- The inclusions of an orthogonal bicone are isometries. -/
@[reassoc]
theorem ι_comp_dagger_ι (hc : c.IsOrthogonal) (j : J) : c.ι j ≫ dagger (c.ι j) = 𝟙 (F j) := by
  rw [hc.dagger_ι, bicone_ι_π_self]

/-- The inclusions of an orthogonal bicone have mutually orthogonal ranges. -/
@[reassoc]
theorem ι_comp_dagger_ι_of_ne (hc : c.IsOrthogonal) {j k : J} (h : j ≠ k) :
    c.ι j ≫ dagger (c.ι k) = 0 := by
  rw [hc.dagger_ι, bicone_ι_π_ne c h]

/-- A dagger functor sends orthogonal bicones to orthogonal bicones. -/
theorem map {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D] [DaggerCategory D]
    (G : C ⥤ D) [G.PreservesZeroMorphisms] [G.PreservesDagger] (hc : c.IsOrthogonal) :
    (G.mapBicone c).IsOrthogonal := fun j =>
  (G.map_dagger (c.π j)).symm.trans (congrArg G.map (hc.dagger_π j))

/-- The comparison isomorphism between the points of two orthogonal limit bicones of the same
family is unitary. -/
theorem isUnitary_conePointUniqueUpToIso_hom {d : Bicone F} (hc : c.IsOrthogonal)
    (hd : d.IsOrthogonal) (hc' : IsLimit c.toCone) (hd' : IsLimit d.toCone) :
    IsUnitary (hc'.conePointUniqueUpToIso hd').hom := by
  rw [Iso.isUnitary_hom_iff]
  refine hc'.hom_ext fun ⟨j⟩ => ?_
  rw [IsLimit.conePointUniqueUpToIso_inv_comp]
  simp [← hc.dagger_ι, ← dagger_comp, hd.dagger_ι]

end IsOrthogonal

end CategoryTheory.Limits.Bicone

namespace TauCeti

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [DaggerCategory C]
variable {J : Type w}

/-- A family of objects of a dagger category *has an orthogonal sum* when it has a limit bicone
whose inclusions are the daggers of its projections. -/
class HasOrthogonalBiproduct (F : J → C) : Prop where
  /-- Some limit bicone of the family is orthogonal. -/
  exists_isOrthogonal : ∃ b : LimitBicone F, b.bicone.IsOrthogonal

namespace HasOrthogonalBiproduct

/-- A chosen orthogonal limit bicone of a family with an orthogonal sum. -/
noncomputable def limitBicone (F : J → C) [HasOrthogonalBiproduct F] : LimitBicone F :=
  (exists_isOrthogonal (F := F)).choose

/-- The chosen limit bicone of a family with an orthogonal sum is orthogonal. -/
theorem isOrthogonal_limitBicone (F : J → C) [HasOrthogonalBiproduct F] :
    (limitBicone F).bicone.IsOrthogonal :=
  (exists_isOrthogonal (F := F)).choose_spec

/-- A family with an orthogonal sum has a biproduct. -/
theorem hasBiproduct (F : J → C) [HasOrthogonalBiproduct F] : HasBiproduct F :=
  .mk (limitBicone F)

/-- Reindexing a family with an orthogonal sum along an equivalence gives a family with an
orthogonal sum. -/
theorem comp_equiv {K : Type*} (F : K → C) [HasOrthogonalBiproduct F] (e : J ≃ K) :
    HasOrthogonalBiproduct (F ∘ e) :=
  ⟨⟨⟨(limitBicone F).bicone.whisker e,
    ((limitBicone F).bicone.whiskerIsBilimitIff e).invFun (limitBicone F).isBilimit⟩,
    fun j => isOrthogonal_limitBicone F (e j)⟩⟩

end HasOrthogonalBiproduct

variable (C) in
/-- A dagger category *has finite orthogonal sums* when every finite family of its objects has an
orthogonal sum. -/
class HasFiniteOrthogonalBiproducts : Prop where
  /-- Every family indexed by `Fin n` has an orthogonal sum. -/
  out : ∀ (n : ℕ) (F : Fin n → C), HasOrthogonalBiproduct F

/-- In a dagger category with finite orthogonal sums, every finite family has an orthogonal
sum. -/
instance (priority := 100) HasFiniteOrthogonalBiproducts.hasOrthogonalBiproduct
    [HasFiniteOrthogonalBiproducts C] [Finite J] (F : J → C) : HasOrthogonalBiproduct F := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have := HasFiniteOrthogonalBiproducts.out n (F ∘ e.symm)
  simpa only [Function.comp_def, e.symm_apply_apply] using
    HasOrthogonalBiproduct.comp_equiv (F ∘ e.symm) e

variable (C) in
/-- A dagger category with finite orthogonal sums has finite biproducts. -/
theorem HasFiniteOrthogonalBiproducts.hasFiniteBiproducts [HasFiniteOrthogonalBiproducts C] :
    HasFiniteBiproducts C :=
  ⟨fun _ => ⟨fun F => HasOrthogonalBiproduct.hasBiproduct F⟩⟩

end TauCeti
