/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Opens
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Singular simplices of subspaces

The singular simplices of a subspace are characterized by the image of their underlying maps.
This identifies the range subcomplex of a subspace inclusion in a singular simplicial set. A
singular simplex whose image lies in an open set `V` corestricts to a singular simplex of `V`
(`TopCat.toSSetObjCodRestrict`), inverse to the map induced by the inclusion of `V`.
-/

public section

open CategoryTheory Limits Topology TopologicalSpace

universe u

namespace TopCat

variable {X : TopCat.{u}}

/-- A singular simplex belongs to the range of a subspace inclusion exactly when its image is
contained in the subspace. -/
lemma mem_range_toSSet_subtypeVal_iff (S : Set X) (n : SimplexCategoryᵒᵖ)
    (σ : (toSSet.obj X).obj n) :
    σ ∈ (SSet.Subcomplex.range
      (toSSet.map (ofHom (ContinuousMap.subtypeVal S)))).obj n ↔
      Set.range (X.toSSetObjEquiv n σ) ⊆ S := by
  rw [Subfunctor.range_obj,
    (IsInducing.subtypeVal : IsInducing
      (ofHom (ContinuousMap.subtypeVal S))).mem_range_toSSet_map_app_iff n σ]
  rw [ConcreteCategory.hom_ofHom,
    show Set.range (⇑(ContinuousMap.subtypeVal S)) = S from Subtype.range_coe]

section Opens

variable {V : Opens X} {n : SimplexCategoryᵒᵖ}

/-- A singular simplex of `X` whose image lies in an open set `V`, as a singular simplex of `V`. -/
noncomputable def toSSetObjCodRestrict (σ : (toSSet.obj X).obj n)
    (h : Set.range (X.toSSetObjEquiv n σ) ⊆ V) : (toSSet.obj ((Opens.toTopCat X).obj V)).obj n :=
  (toSSetObjEquiv _ n).symm
    ⟨Set.codRestrict _ _ fun z ↦ h ⟨z, rfl⟩, (map_continuous _).codRestrict _⟩

/-- The corestriction of a singular simplex to an open set `V` has the same underlying map,
viewed in `X`. -/
@[simp]
lemma coe_toSSetObjEquiv_toSSetObjCodRestrict (σ : (toSSet.obj X).obj n)
    (h : Set.range (X.toSSetObjEquiv n σ) ⊆ V) (z : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    (toSSetObjEquiv _ n (toSSetObjCodRestrict σ h) z).1 = X.toSSetObjEquiv n σ z := by
  rw [toSSetObjCodRestrict, Equiv.apply_symm_apply]
  -- Evaluating a corestriction and coercing back to `X` evaluates the original map.
  rfl

/-- The image in `X` of a singular simplex of an open set `V` lies in `V`. -/
lemma range_toSSetObjEquiv_toSSet_map_inclusion'_subset
    (τ : (toSSet.obj ((Opens.toTopCat X).obj V)).obj n) :
    Set.range (X.toSSetObjEquiv n ((toSSet.map (Opens.inclusion' V)).app n τ)) ⊆ V := by
  rintro _ ⟨z, rfl⟩
  exact (toSSetObjEquiv _ n τ z).2

/-- The corestriction of a singular simplex to an open set `V`, followed by the inclusion of `V`,
is the singular simplex itself. -/
@[simp]
lemma toSSet_map_inclusion'_toSSetObjCodRestrict (σ : (toSSet.obj X).obj n)
    (h : Set.range (X.toSSetObjEquiv n σ) ⊆ V) :
    (toSSet.map (Opens.inclusion' V)).app n (toSSetObjCodRestrict σ h) = σ := by
  apply (X.toSSetObjEquiv n).injective
  ext z
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  exact coe_toSSetObjEquiv_toSSetObjCodRestrict σ h z

/-- The corestriction to an open set `V` of the image of a singular simplex `τ` of `V` is `τ`. -/
lemma toSSetObjCodRestrict_eq {σ : (toSSet.obj X).obj n}
    (h : Set.range (X.toSSetObjEquiv n σ) ⊆ V) {τ : (toSSet.obj ((Opens.toTopCat X).obj V)).obj n}
    (e : (toSSet.map (Opens.inclusion' V)).app n τ = σ) :
    toSSetObjCodRestrict σ h = τ := by
  subst e
  apply (toSSetObjEquiv _ n).injective
  ext z
  apply Subtype.ext
  rw [coe_toSSetObjEquiv_toSSetObjCodRestrict, TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  -- Evaluating the composite with the inclusion of `V` is coercing the value of `τ`.
  rfl

/-- Corestricting a singular simplex to an open set `V` and then including `V` in an open set
`W ⊇ V` is corestricting it to `W`. -/
@[simp]
lemma toSSet_map_homOfLE_toSSetObjCodRestrict {W : Opens X} (hVW : V ≤ W)
    (σ : (toSSet.obj X).obj n) (h : Set.range (X.toSSetObjEquiv n σ) ⊆ V) :
    (toSSet.map ((Opens.toTopCat X).map (homOfLE hVW))).app n (toSSetObjCodRestrict σ h) =
      toSSetObjCodRestrict σ (h.trans hVW) := by
  apply (toSSetObjEquiv _ n).injective
  ext z
  apply Subtype.ext
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app, coe_toSSetObjEquiv_toSSetObjCodRestrict]
  exact coe_toSSetObjEquiv_toSSetObjCodRestrict σ h z

end Opens

end TopCat
