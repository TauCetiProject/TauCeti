/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.Combinatorics.Quiver.Subquiver
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Topology.IsLocalHomeomorph

/-!
# Products of topological groupoids

Let `C` and `D` be categories whose objects and total arrows carry topologies, as for topological
groupoids. The objects of the product category `C × D` carry the product topology. A total arrow
of `C × D` is a pair of total arrows of `C` and `D`, and `TauCeti.totalProdHomeomorph` gives the
total arrows of `C × D` the product topology of `Quiver.Total C × Quiver.Total D`.

The hypotheses of a Hausdorff proper étale presentation pass to products: the total arrows
remain Hausdorff and second countable, source and target remain local homeomorphisms
(`TauCeti.isLocalHomeomorph_source_prod`, `TauCeti.isLocalHomeomorph_target_prod`), the
source-target map remains proper (`TauCeti.isProperMap_source_target_prod`), and continuity of
source, target, units, composition and inversion is inherited. Isotropy groups of products are
products of isotropy groups, with every arrow of both factors retained.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1.
-/

public section

open CategoryTheory Topology

namespace TauCeti

variable {C D : Type*} [Category C] [Category D]

variable [TopologicalSpace (Quiver.Total C)] [TopologicalSpace (Quiver.Total D)]

/-- The total arrows of a product category carry the product topology of the pairs of total
arrows of the factors. -/
instance instTopologicalSpaceTotalProd : TopologicalSpace (Quiver.Total (C × D)) :=
  .induced (fun a ↦ ((⟨a.left.1, a.right.1, a.hom.1⟩ : Quiver.Total C),
    (⟨a.left.2, a.right.2, a.hom.2⟩ : Quiver.Total D))) inferInstance

variable (C D) in
/-- The total arrows of a product category are homeomorphic to pairs of total arrows of the
factors. -/
def totalProdHomeomorph : Quiver.Total (C × D) ≃ₜ Quiver.Total C × Quiver.Total D where
  toFun a := (⟨a.left.1, a.right.1, a.hom.1⟩, ⟨a.left.2, a.right.2, a.hom.2⟩)
  invFun p := ⟨(p.1.left, p.2.left), (p.1.right, p.2.right), (p.1.hom, p.2.hom)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    refine continuous_induced_rng.mpr ?_
    exact continuous_id

/-- The homeomorphism reads off the components of a total arrow of a product category. -/
@[simp]
theorem totalProdHomeomorph_apply (a : Quiver.Total (C × D)) :
    totalProdHomeomorph C D a =
      (⟨a.left.1, a.right.1, a.hom.1⟩, ⟨a.left.2, a.right.2, a.hom.2⟩) := (rfl)

/-- The inverse homeomorphism pairs a total arrow of each factor. -/
@[simp]
theorem totalProdHomeomorph_symm_apply (p : Quiver.Total C × Quiver.Total D) :
    (totalProdHomeomorph C D).symm p =
      ⟨(p.1.left, p.2.left), (p.1.right, p.2.right), (p.1.hom, p.2.hom)⟩ := (rfl)

/-- The total arrows of a product of categories with Hausdorff total arrows are Hausdorff. -/
instance instT2SpaceTotalProd [T2Space (Quiver.Total C)] [T2Space (Quiver.Total D)] :
    T2Space (Quiver.Total (C × D)) :=
  (totalProdHomeomorph C D).symm.t2Space

/-- The total arrows of a product of categories with second-countable total arrows are second
countable. -/
instance instSecondCountableTopologyTotalProd [SecondCountableTopology (Quiver.Total C)]
    [SecondCountableTopology (Quiver.Total D)] :
    SecondCountableTopology (Quiver.Total (C × D)) :=
  (totalProdHomeomorph C D).isInducing.secondCountableTopology

/-- Composition in a product category is continuous on composable pairs when composition in both
factors is. -/
theorem continuous_comp_prod
    (hC : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total C))
    (hD : Continuous fun p : {p : Quiver.Total D × Quiver.Total D // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total D)) :
    Continuous fun p : {p : Quiver.Total (C × D) × Quiver.Total (C × D) //
        p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ :
        Quiver.Total (C × D)) := by
  let e := totalProdHomeomorph C D
  let gC := fun p : {p : Quiver.Total (C × D) × Quiver.Total (C × D) // p.1.right = p.2.left} ↦
    (⟨((e p.1.1).1, (e p.1.2).1), congrArg Prod.fst p.2⟩ :
      {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left})
  let gD := fun p : {p : Quiver.Total (C × D) × Quiver.Total (C × D) // p.1.right = p.2.left} ↦
    (⟨((e p.1.1).2, (e p.1.2).2), congrArg Prod.snd p.2⟩ :
      {p : Quiver.Total D × Quiver.Total D // p.1.right = p.2.left})
  have h₁ : Continuous fun p : {p : Quiver.Total (C × D) × Quiver.Total (C × D) //
      p.1.right = p.2.left} ↦ e p.1.1 := e.continuous.comp (continuous_fst.comp
    continuous_subtype_val)
  have h₂ : Continuous fun p : {p : Quiver.Total (C × D) × Quiver.Total (C × D) //
      p.1.right = p.2.left} ↦ e p.1.2 := e.continuous.comp (continuous_snd.comp
    continuous_subtype_val)
  have hgC : Continuous gC :=
    ((continuous_fst.comp h₁).prodMk (continuous_fst.comp h₂)).subtype_mk _
  have hgD : Continuous gD :=
    ((continuous_snd.comp h₁).prodMk (continuous_snd.comp h₂)).subtype_mk _
  refine e.isInducing.continuous_iff.mpr ?_
  convert (hC.comp hgC).prodMk (hD.comp hgD) using 1
  funext ⟨⟨⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩, f⟩, ⟨⟨y₁', y₂'⟩, ⟨z₁, z₂⟩, f'⟩⟩, h⟩
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp [e, gC, gD]

/-- Inversion in a product of groupoids is continuous when inversion in both factors is. -/
theorem continuous_inverse_prod {G H : Type*} [Groupoid G] [Groupoid H]
    [TopologicalSpace (Quiver.Total G)] [TopologicalSpace (Quiver.Total H)]
    (hG : Continuous fun a : Quiver.Total G ↦ (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total G))
    (hH : Continuous fun a : Quiver.Total H ↦ (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total H)) :
    Continuous fun a : Quiver.Total (G × H) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (G × H)) := by
  refine (totalProdHomeomorph G H).isInducing.continuous_iff.mpr ?_
  convert (hG.comp (continuous_fst.comp (totalProdHomeomorph G H).continuous)).prodMk
    (hH.comp (continuous_snd.comp (totalProdHomeomorph G H).continuous)) using 1
  funext a
  simp only [Function.comp_apply, ← Groupoid.inv_eq_inv]
  rfl

variable [TopologicalSpace C] [TopologicalSpace D]

/-- The source of a product category is continuous when the sources of both factors are. -/
theorem continuous_source_prod (hC : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (hD : Continuous (Quiver.Total.left : Quiver.Total D → D)) :
    Continuous (Quiver.Total.left : Quiver.Total (C × D) → C × D) :=
  -- The source of a product is `Prod.map` of the sources, read through `totalProdHomeomorph`.
  (hC.prodMap hD).comp (totalProdHomeomorph C D).continuous

/-- The target of a product category is continuous when the targets of both factors are. -/
theorem continuous_target_prod (hC : Continuous (Quiver.Total.right : Quiver.Total C → C))
    (hD : Continuous (Quiver.Total.right : Quiver.Total D → D)) :
    Continuous (Quiver.Total.right : Quiver.Total (C × D) → C × D) :=
  (hC.prodMap hD).comp (totalProdHomeomorph C D).continuous

/-- The source of a product category is a local homeomorphism when the sources of both factors
are. -/
theorem isLocalHomeomorph_source_prod
    (hC : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (hD : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total D → D)) :
    IsLocalHomeomorph (Quiver.Total.left : Quiver.Total (C × D) → C × D) :=
  (hC.prodMap hD).comp (totalProdHomeomorph C D).isLocalHomeomorph

/-- The target of a product category is a local homeomorphism when the targets of both factors
are. -/
theorem isLocalHomeomorph_target_prod
    (hC : IsLocalHomeomorph (Quiver.Total.right : Quiver.Total C → C))
    (hD : IsLocalHomeomorph (Quiver.Total.right : Quiver.Total D → D)) :
    IsLocalHomeomorph (Quiver.Total.right : Quiver.Total (C × D) → C × D) :=
  (hC.prodMap hD).comp (totalProdHomeomorph C D).isLocalHomeomorph

/-- The source-target map of a product category is proper when those of both factors are. -/
theorem isProperMap_source_target_prod
    (hC : IsProperMap (fun a : Quiver.Total C ↦ (a.left, a.right)))
    (hD : IsProperMap (fun a : Quiver.Total D ↦ (a.left, a.right))) :
    IsProperMap (fun a : Quiver.Total (C × D) ↦ (a.left, a.right)) :=
  -- Componentwise, the source-target map is the product of those of the factors, up to the
  -- shuffle `(C × C) × (D × D) ≃ₜ (C × D) × (C × D)`.
  (Homeomorph.prodProdProdComm C C D D).isProperMap.comp
    ((hC.prodMap hD).comp (totalProdHomeomorph C D).isProperMap)

/-- The unit map of a product category is continuous when the unit maps of both factors are. -/
theorem continuous_unit_prod (hC : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
    (hD : Continuous fun x : D ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total D)) :
    Continuous fun x : C × D ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total (C × D)) :=
  -- Units of a product are pairs of units, by `CategoryTheory.prod_id`.
  (totalProdHomeomorph C D).isInducing.continuous_iff.mpr (hC.prodMap hD)

end TauCeti
