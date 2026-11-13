/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.Fin.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.IsCone
public import TauCeti.AlgebraicTopology.SimplicialComplex.Maps
import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Basic
public import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Lattice

/-!
# Ordered products of abstract simplicial complexes

The ordered product of two simplicial complexes is the standard staircase triangulation of their
product. Its vertices are pairs of vertices. A finite set of pairs is a face when both coordinate
projections are faces and the pairs form a chain for the coordinatewise order. The chain condition
is essential: without it, the four vertices of a square would span a tetrahedron rather than two
triangles.

This file constructs the product first for `PreAbstractSimplicialComplex`, then for
`AbstractSimplicialComplex`. It also supplies the simplicial coordinate projections,
fixed-coordinate inclusions, and the ordered cylinder obtained by taking the second factor to be
the standard one-simplex on `Fin 2`. The faces of the ordered cylinder are described explicitly
as the subsets of staircase simplices, which switch from the initial to the terminal end of the
interval at one vertex of a face of the base.

The construction is the simplicial product used in collapse arguments. In particular, the ordered
cylinder is the simplicial model of the product `K × I` in the statement of Zeeman's conjecture
(`Zeeman`). The definition follows the ordered (staircase) triangulation convention in
Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2. No claim about the
realization of this product is made here; for a product with finitely many faces,
`Realization.Product.Homeomorph` identifies its realization with the product of realizations.

## Main definitions

* `PreAbstractSimplicialComplex.orderedProd`: the ordered product of two precomplexes.
* `AbstractSimplicialComplex.orderedProd`: the ordered product of two complexes.
* `AbstractSimplicialComplex.orderedCylinder`: product with the standard one-simplex.
* `Finset.cylinderStaircase`: the staircase simplices of the prism on a finite set.
* `AbstractSimplicialComplex.mem_orderedCylinder_iff_exists_subset_cylinderStaircase`: the faces
  of the ordered cylinder are the nonempty subsets of the staircases over faces of the base.
* `AbstractSimplicialComplex.isCone_orderedCylinder_of_isCone`: taking the ordered cylinder
  preserves a cone whose apex is greatest.
* `PreAbstractSimplicialComplex.SimplicialMap.orderedProdFst` and
  `orderedProdSnd`: the coordinate projections.
* `PreAbstractSimplicialComplex.SimplicialMap.prodMkLeft` and `prodMkRight`:
  fixed-coordinate inclusions into an ordered product.
-/

public section

namespace PreAbstractSimplicialComplex

variable {α β γ δ : Type*}

section OrderedProd

variable [LinearOrder α] [LinearOrder β]

/-- The ordered product of two pre-abstract simplicial complexes.

A finite set of pairs is a face exactly when its two coordinate images are faces of the factors
and it is a chain for the coordinatewise order on the product. The linear orders are data in the
construction: changing them can change the triangulation, though not its intended PL type. -/
public def orderedProd (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) : PreAbstractSimplicialComplex (α × β) where
  faces := {σ | σ.image Prod.fst ∈ K ∧ σ.image Prod.snd ∈ L ∧
    IsChain (· ≤ ·) (σ : Set (α × β))}
  isRelLowerSet_faces := by
    rintro σ ⟨hK, hL, hchain⟩
    refine ⟨Finset.image_nonempty.mp (K.isRelLowerSet_faces hK).1, fun τ hτσ hτ => ?_⟩
    refine ⟨?_, ?_, hchain.mono (Finset.coe_subset.mpr hτσ)⟩
    · exact (K.isRelLowerSet_faces hK).2 (Finset.image_subset_image hτσ)
        (Finset.image_nonempty.mpr hτ)
    · exact (L.isRelLowerSet_faces hL).2 (Finset.image_subset_image hτσ)
        (Finset.image_nonempty.mpr hτ)

variable {K K' : PreAbstractSimplicialComplex α}
  {L L' : PreAbstractSimplicialComplex β}

/-- Membership in an ordered product is characterized by the two projected face conditions and
the staircase chain condition. -/
@[simp]
theorem mem_orderedProd_iff {σ : Finset (α × β)} :
    σ ∈ orderedProd K L ↔ σ.image Prod.fst ∈ K ∧ σ.image Prod.snd ∈ L ∧
      IsChain (· ≤ ·) (σ : Set (α × β)) :=
  Iff.rfl

/-- The first-coordinate image of a face of an ordered product is a face of the first factor. -/
theorem image_fst_mem_of_mem_orderedProd {σ : Finset (α × β)}
    (hσ : σ ∈ orderedProd K L) : σ.image Prod.fst ∈ K :=
  (mem_orderedProd_iff.mp hσ).1

/-- The second-coordinate image of a face of an ordered product is a face of the second factor. -/
theorem image_snd_mem_of_mem_orderedProd {σ : Finset (α × β)}
    (hσ : σ ∈ orderedProd K L) : σ.image Prod.snd ∈ L :=
  (mem_orderedProd_iff.mp hσ).2.1

/-- Every face of an ordered product is a chain for the coordinatewise order. -/
theorem isChain_of_mem_orderedProd {σ : Finset (α × β)}
    (hσ : σ ∈ orderedProd K L) : IsChain (· ≤ ·) (σ : Set (α × β)) :=
  (mem_orderedProd_iff.mp hσ).2.2

/-- Ordered product is monotone in both factors. -/
theorem orderedProd_mono (hK : K ≤ K') (hL : L ≤ L') :
    orderedProd K L ≤ orderedProd K' L' := by
  rintro σ ⟨hσK, hσL, hchain⟩
  exact ⟨hK hσK, hL hσL, hchain⟩

/-- An ordered product of finite-face precomplexes has finitely many faces.

Every product face is a subset of the product of the finite sets of vertices used by the two
factor complexes.  This is the finiteness input for compactness of its geometric realization; the
ambient vertex types themselves need not be finite. -/
theorem finite_faces_orderedProd (hK : K.faces.Finite) (hL : L.faces.Finite) :
    (orderedProd K L).faces.Finite := by
  classical
  let VK : Set α := ⋃ σ ∈ K.faces, (σ : Set α)
  let VL : Set β := ⋃ τ ∈ L.faces, (τ : Set β)
  have hVK : VK.Finite := by
    dsimp [VK]
    exact hK.biUnion fun σ _ => σ.finite_toSet
  have hVL : VL.Finite := by
    dsimp [VL]
    exact hL.biUnion fun τ _ => τ.finite_toSet
  let V := hVK.toFinset.product hVL.toFinset
  refine (Finset.finite_toSet V.powerset).subset ?_
  intro σ hσ
  rw [Finset.mem_coe, Finset.mem_powerset]
  intro p hp
  have hpK : p.1 ∈ VK := by
    dsimp [VK]
    refine Set.mem_iUnion.2 ⟨σ.image Prod.fst, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
    · exact image_fst_mem_of_mem_orderedProd hσ
    · exact Finset.mem_image.2 ⟨p, hp, rfl⟩
  have hpL : p.2 ∈ VL := by
    dsimp [VL]
    refine Set.mem_iUnion.2 ⟨σ.image Prod.snd, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
    · exact image_snd_mem_of_mem_orderedProd hσ
    · exact Finset.mem_image.2 ⟨p, hp, rfl⟩
  exact Finset.mem_product.2 ⟨hVK.mem_toFinset.2 hpK, hVL.mem_toFinset.2 hpL⟩

end OrderedProd

namespace SimplicialMap

section Projections

variable [LinearOrder α] [LinearOrder β]
variable {K : PreAbstractSimplicialComplex α} {L : PreAbstractSimplicialComplex β}

/-- The first coordinate projection from an ordered product is simplicial. -/
public def orderedProdFst (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) : SimplicialMap (orderedProd K L) K where
  toFun := Prod.fst
  map_face' := fun _ hσ ↦ image_fst_mem_of_mem_orderedProd (K := K) (L := L) hσ

@[simp]
theorem coe_orderedProdFst (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) : ⇑(orderedProdFst K L) = Prod.fst := by
  simp only [orderedProdFst, coe_mk]

@[simp]
theorem orderedProdFst_apply (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) (p : α × β) : orderedProdFst K L p = p.1 :=
  congrFun (coe_orderedProdFst K L) p

/-- The second coordinate projection from an ordered product is simplicial. -/
public def orderedProdSnd (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) : SimplicialMap (orderedProd K L) L where
  toFun := Prod.snd
  map_face' := fun _ hσ ↦ image_snd_mem_of_mem_orderedProd (K := K) (L := L) hσ

@[simp]
theorem coe_orderedProdSnd (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) : ⇑(orderedProdSnd K L) = Prod.snd := by
  simp only [orderedProdSnd, coe_mk]

@[simp]
theorem orderedProdSnd_apply (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) (p : α × β) : orderedProdSnd K L p = p.2 :=
  congrFun (coe_orderedProdSnd K L) p

end Projections

section ProdMkLeft

variable [LinearOrder α] [LinearOrder β]
variable {K : PreAbstractSimplicialComplex α} {L : PreAbstractSimplicialComplex β}

/-- Fixing a vertex `b` of the second factor gives the simplicial inclusion `a ↦ (a, b)` of the
first factor into the ordered product. -/
public def prodMkLeft (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β)
    (b : β) (hb : ({b} : Finset β) ∈ L) : SimplicialMap K (orderedProd K L) where
  toFun := fun a => (a, b)
  map_face' := by
    intro σ hσ
    have hσne := (K.isRelLowerSet_faces hσ).1
    rw [mem_orderedProd_iff]
    refine ⟨?_, ?_, ?_⟩
    · simpa [Finset.image_image, Function.comp_def] using hσ
    · simpa [Finset.image_image, Function.comp_def, Finset.image_const hσne b] using hb
    · rw [Finset.coe_image]
      have hmono : Monotone (fun a : α => (a, b)) := fun _ _ h ↦ ⟨h, le_rfl⟩
      exact hmono.isChain_image (isChain_of_trichotomous (σ : Set α))

@[simp]
theorem coe_prodMkLeft (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) (b : β) (hb : ({b} : Finset β) ∈ L) :
    ⇑(prodMkLeft K L b hb) = fun a ↦ (a, b) := by
  simp only [prodMkLeft, coe_mk]

@[simp]
theorem prodMkLeft_apply (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) (b : β) (hb : ({b} : Finset β) ∈ L) (a : α) :
    prodMkLeft K L b hb a = (a, b) :=
  congrFun (coe_prodMkLeft K L b hb) a

/-- The fixed-second-coordinate copy of the first factor is a subcomplex of the ordered product. -/
theorem map_prodMkLeft_le_orderedProd (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) (b : β) (hb : ({b} : Finset β) ∈ L) :
    K.map (fun a => (a, b)) ≤ orderedProd K L :=
  (prodMkLeft K L b hb).map_le

end ProdMkLeft

section ProdMkRight

variable [LinearOrder α] [LinearOrder β]
variable {K : PreAbstractSimplicialComplex α} {L : PreAbstractSimplicialComplex β}

/-- Fixing a vertex `a` of the first factor gives the simplicial inclusion `b ↦ (a, b)` of the
second factor into the ordered product. -/
public def prodMkRight (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β)
    (a : α) (ha : ({a} : Finset α) ∈ K) : SimplicialMap L (orderedProd K L) where
  toFun := fun b => (a, b)
  map_face' := by
    intro σ hσ
    have hσne := (L.isRelLowerSet_faces hσ).1
    rw [mem_orderedProd_iff]
    refine ⟨?_, ?_, ?_⟩
    · simpa [Finset.image_image, Function.comp_def, Finset.image_const hσne a] using ha
    · simpa [Finset.image_image, Function.comp_def] using hσ
    · rw [Finset.coe_image]
      have hmono : Monotone (fun b : β => (a, b)) := fun _ _ h ↦ ⟨le_rfl, h⟩
      exact hmono.isChain_image (isChain_of_trichotomous (σ : Set β))

@[simp]
theorem coe_prodMkRight (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) (a : α) (ha : ({a} : Finset α) ∈ K) :
    ⇑(prodMkRight K L a ha) = fun b ↦ (a, b) := by
  simp only [prodMkRight, coe_mk]

@[simp]
theorem prodMkRight_apply (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) (a : α) (ha : ({a} : Finset α) ∈ K) (b : β) :
    prodMkRight K L a ha b = (a, b) :=
  congrFun (coe_prodMkRight K L a ha) b

/-- The fixed-first-coordinate copy of the second factor is a subcomplex of the ordered product. -/
theorem map_prodMkRight_le_orderedProd (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) (a : α) (ha : ({a} : Finset α) ∈ K) :
    L.map (fun b => (a, b)) ≤ orderedProd K L :=
  (prodMkRight K L a ha).map_le

end ProdMkRight

section OrderedProdMap

variable [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]
variable {K : PreAbstractSimplicialComplex α} {L : PreAbstractSimplicialComplex β}

/-- Monotone simplicial maps induce a simplicial map between ordered products. Monotonicity is
needed because the product triangulation depends on the chosen vertex orders. -/
public def orderedProdMap {Kγ : PreAbstractSimplicialComplex γ}
    {Lδ : PreAbstractSimplicialComplex δ} (f : SimplicialMap K Kγ)
    (g : SimplicialMap L Lδ) (hf : Monotone f) (hg : Monotone g) :
    SimplicialMap (orderedProd K L) (orderedProd Kγ Lδ) where
  toFun := fun p => (f p.1, g p.2)
  map_face' := by
    intro σ hσ
    rw [mem_orderedProd_iff] at hσ ⊢
    refine ⟨?_, ?_, ?_⟩
    · simpa [Finset.image_image, Function.comp_def] using f.map_face hσ.1
    · simpa [Finset.image_image, Function.comp_def] using g.map_face hσ.2.1
    · rw [Finset.coe_image]
      have hmono : Monotone (fun p : α × β => (f p.1, g p.2)) :=
        fun _ _ h ↦ ⟨hf h.1, hg h.2⟩
      exact hmono.isChain_image hσ.2.2

@[simp]
theorem coe_orderedProdMap {Kγ : PreAbstractSimplicialComplex γ}
    {Lδ : PreAbstractSimplicialComplex δ} (f : SimplicialMap K Kγ)
    (g : SimplicialMap L Lδ) (hf : Monotone f) (hg : Monotone g) :
    ⇑(orderedProdMap f g hf hg) = fun p ↦ (f p.1, g p.2) := by
  simp only [orderedProdMap, coe_mk]

@[simp]
theorem orderedProdMap_apply {Kγ : PreAbstractSimplicialComplex γ}
    {Lδ : PreAbstractSimplicialComplex δ} (f : SimplicialMap K Kγ)
    (g : SimplicialMap L Lδ) (hf : Monotone f) (hg : Monotone g) (p : α × β) :
    orderedProdMap f g hf hg p = (f p.1, g p.2) :=
  congrFun (coe_orderedProdMap f g hf hg) p

end OrderedProdMap

end SimplicialMap

end PreAbstractSimplicialComplex

namespace Finset

variable {α : Type*} [LinearOrder α]

/-- The staircase simplex of the prism on `V` that passes from the initial to the terminal end of
the interval at `k`: the vertices `(x, 0)` with `x ≤ k` and `(x, 1)` with `k ≤ x`, for `x ∈ V`.
For `k ∈ V` these are the top-dimensional simplices of the ordered cylinder on the simplex `V`.
The body is exposed so that staircases of explicit complexes can be evaluated by `decide`. -/
@[expose] def cylinderStaircase (V : Finset α) (k : α) : Finset (α × Fin 2) :=
  V.filter (· ≤ k) ×ˢ {0} ∪ V.filter (k ≤ ·) ×ˢ {1}

/-- Membership in a staircase: a vertex of the initial end at or below the switching vertex, or a
vertex of the terminal end at or above it. -/
@[simp]
theorem mem_cylinderStaircase {V : Finset α} {k : α} {p : α × Fin 2} :
    p ∈ cylinderStaircase V k ↔ p.1 ∈ V ∧ (p.2 = 0 ∧ p.1 ≤ k ∨ p.2 = 1 ∧ k ≤ p.1) := by
  simp only [cylinderStaircase, Finset.mem_union, Finset.mem_product, Finset.mem_filter,
    Finset.mem_singleton]
  tauto

/-- Staircases are monotone in the vertex set. -/
theorem cylinderStaircase_mono {V W : Finset α} (h : V ⊆ W) (k : α) :
    cylinderStaircase V k ⊆ cylinderStaircase W k := fun _ hp =>
  mem_cylinderStaircase.mpr ⟨h (mem_cylinderStaircase.mp hp).1, (mem_cylinderStaircase.mp hp).2⟩

end Finset

namespace AbstractSimplicialComplex

variable {α β : Type*}

section OrderedProd

variable [LinearOrder α] [LinearOrder β]

/-- The ordered product of two abstract simplicial complexes. -/
public def orderedProd (K : AbstractSimplicialComplex α) (L : AbstractSimplicialComplex β) :
    AbstractSimplicialComplex (α × β) :=
  PreAbstractSimplicialComplex.toAbstractSimplicialComplex (α × β)
    (PreAbstractSimplicialComplex.orderedProd K.toPreAbstractSimplicialComplex
      L.toPreAbstractSimplicialComplex) fun p => by
        exact PreAbstractSimplicialComplex.mem_orderedProd_iff.mpr
          ⟨by rw [Finset.image_singleton]; exact K.singleton_mem p.1,
            by rw [Finset.image_singleton]; exact L.singleton_mem p.2, by simp⟩

variable {K K' : AbstractSimplicialComplex α} {L L' : AbstractSimplicialComplex β}

/-- Forgetting that the ordered product contains every singleton recovers the product of the
underlying precomplexes. -/
@[simp]
theorem orderedProd_toPreAbstractSimplicialComplex :
    (orderedProd K L).toPreAbstractSimplicialComplex =
      PreAbstractSimplicialComplex.orderedProd K.toPreAbstractSimplicialComplex
        L.toPreAbstractSimplicialComplex := by
  ext σ
  rfl

/-- Membership in an abstract ordered product has the same projected-face and chain
characterization as for precomplexes. -/
@[simp]
theorem mem_orderedProd_iff {σ : Finset (α × β)} :
    σ ∈ orderedProd K L ↔ σ.image Prod.fst ∈ K ∧ σ.image Prod.snd ∈ L ∧
      IsChain (· ≤ ·) (σ : Set (α × β)) := by
  simp only [← mem_toPreAbstractSimplicialComplex,
    orderedProd_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.mem_orderedProd_iff

/-- The first-coordinate image of a face of an abstract ordered product is a face of the first
factor. -/
theorem image_fst_mem_of_mem_orderedProd {σ : Finset (α × β)}
    (hσ : σ ∈ orderedProd K L) : σ.image Prod.fst ∈ K :=
  (mem_orderedProd_iff.mp hσ).1

/-- The second-coordinate image of a face of an abstract ordered product is a face of the second
factor. -/
theorem image_snd_mem_of_mem_orderedProd {σ : Finset (α × β)}
    (hσ : σ ∈ orderedProd K L) : σ.image Prod.snd ∈ L :=
  (mem_orderedProd_iff.mp hσ).2.1

/-- Every face of an abstract ordered product is a chain for the coordinatewise order. -/
theorem isChain_of_mem_orderedProd {σ : Finset (α × β)}
    (hσ : σ ∈ orderedProd K L) : IsChain (· ≤ ·) (σ : Set (α × β)) :=
  (mem_orderedProd_iff.mp hσ).2.2

/-- Ordered product is monotone in both abstract simplicial complexes. -/
theorem orderedProd_mono (hK : K ≤ K') (hL : L ≤ L') :
    orderedProd K L ≤ orderedProd K' L' := by
  rw [← _root_.AbstractSimplicialComplex.toPreAbstractSimplicialComplex_le_iff]
  rw [orderedProd_toPreAbstractSimplicialComplex, orderedProd_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.orderedProd_mono hK hL

/-- An ordered product of finite-face abstract complexes has finitely many faces. -/
theorem finite_faces_orderedProd (hK : K.faces.Finite) (hL : L.faces.Finite) :
    (orderedProd K L).faces.Finite := by
  rw [orderedProd_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.finite_faces_orderedProd hK hL

/-- The ordered simplicial cylinder on `K`, obtained by taking its ordered product with the
standard one-simplex on `Fin 2`. -/
def orderedCylinder (K : AbstractSimplicialComplex α) :
    AbstractSimplicialComplex (α × Fin 2) :=
  orderedProd K (⊤ : AbstractSimplicialComplex (Fin 2))

/-- The ordered cylinder is the ordered product with the standard one-simplex. -/
theorem orderedCylinder_def (K : AbstractSimplicialComplex α) :
    K.orderedCylinder = K.orderedProd (⊤ : AbstractSimplicialComplex (Fin 2)) :=
  (rfl)

/-- The underlying precomplex of an ordered cylinder is the ordered product with the top
precomplex on `Fin 2`. -/
@[simp]
theorem orderedCylinder_toPreAbstractSimplicialComplex (K : AbstractSimplicialComplex α) :
    (orderedCylinder K).toPreAbstractSimplicialComplex =
      PreAbstractSimplicialComplex.orderedProd K.toPreAbstractSimplicialComplex ⊤ := by
  rw [orderedCylinder, orderedProd_toPreAbstractSimplicialComplex,
    _root_.AbstractSimplicialComplex.top_toPreAbstractSimplicialComplex]

/-- A face of the ordered cylinder is a face in the first coordinate and a chain in the product
order. The second projection condition is automatic because the interval factor is top. -/
@[simp]
theorem mem_orderedCylinder_iff {σ : Finset (α × Fin 2)} :
    σ ∈ orderedCylinder K ↔ σ.image Prod.fst ∈ K ∧
      IsChain (· ≤ ·) (σ : Set (α × Fin 2)) := by
  rw [orderedCylinder, mem_orderedProd_iff]
  constructor
  · rintro ⟨hK, _, hchain⟩
    exact ⟨hK, hchain⟩
  · rintro ⟨hK, hchain⟩
    refine ⟨hK, ?_, hchain⟩
    rw [← mem_toPreAbstractSimplicialComplex,
      _root_.AbstractSimplicialComplex.top_toPreAbstractSimplicialComplex]
    exact Finset.image_nonempty.mpr (Finset.image_nonempty.mp (K.isRelLowerSet_faces hK).1)

/-- The first-coordinate image of a face of an ordered cylinder is a face of the original
complex. -/
theorem image_fst_mem_of_mem_orderedCylinder {σ : Finset (α × Fin 2)}
    (hσ : σ ∈ orderedCylinder K) : σ.image Prod.fst ∈ K :=
  (mem_orderedCylinder_iff.mp hσ).1

/-- Every face of an ordered cylinder is a chain for the product order. -/
theorem isChain_of_mem_orderedCylinder {σ : Finset (α × Fin 2)}
    (hσ : σ ∈ orderedCylinder K) : IsChain (· ≤ ·) (σ : Set (α × Fin 2)) :=
  (mem_orderedCylinder_iff.mp hσ).2

/-- The ordered cylinder of a finite abstract simplicial complex has finitely many faces. -/
theorem finite_faces_orderedCylinder (hfin : K.faces.Finite) :
    K.orderedCylinder.faces.Finite := by
  rw [orderedCylinder_toPreAbstractSimplicialComplex]
  have htop : (⊤ : PreAbstractSimplicialComplex (Fin 2)).faces.Finite := by
    simpa only [PreAbstractSimplicialComplex.simplex_univ] using
      (PreAbstractSimplicialComplex.finite_faces_simplex (Finset.univ : Finset (Fin 2)))
  exact PreAbstractSimplicialComplex.finite_faces_orderedProd hfin htop

/-- A staircase over a face, switching at one of its vertices, is a face of the ordered
cylinder. -/
theorem cylinderStaircase_mem_orderedCylinder {V : Finset α} {k : α} (hV : V ∈ K) (hk : k ∈ V) :
    V.cylinderStaircase k ∈ K.orderedCylinder := by
  refine mem_orderedCylinder_iff.mpr ⟨?_, ?_⟩
  · refine (K.isRelLowerSet_faces hV).2 (fun x hx => ?_) ⟨k, Finset.mem_image.mpr
      ⟨(k, 0), Finset.mem_cylinderStaircase.mpr ⟨hk, Or.inl ⟨rfl, le_rfl⟩⟩, rfl⟩⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_cylinderStaircase.mp hp).1
  · intro p hp q hq _
    simp only [Finset.mem_coe, Finset.mem_cylinderStaircase] at hp hq
    obtain ⟨-, ⟨hp2, hpk⟩ | ⟨hp2, hkp⟩⟩ := hp <;> obtain ⟨-, ⟨hq2, hqk⟩ | ⟨hq2, hkq⟩⟩ := hq
    · rcases le_total p.1 q.1 with h | h
      · exact Or.inl ⟨h, (hp2.trans hq2.symm).le⟩
      · exact Or.inr ⟨h, (hq2.trans hp2.symm).le⟩
    · exact Or.inl ⟨hpk.trans hkq, hp2 ▸ Fin.zero_le _⟩
    · exact Or.inr ⟨hqk.trans hkp, hq2 ▸ Fin.zero_le _⟩
    · rcases le_total p.1 q.1 with h | h
      · exact Or.inl ⟨h, (hp2.trans hq2.symm).le⟩
      · exact Or.inr ⟨h, (hq2.trans hp2.symm).le⟩

/-- Every face of the ordered cylinder lies in a staircase over its first-coordinate image,
switching at one of the vertices of that image. -/
theorem exists_subset_cylinderStaircase_of_mem_orderedCylinder {σ : Finset (α × Fin 2)}
    (hσ : σ ∈ K.orderedCylinder) :
    ∃ k ∈ σ.image Prod.fst, σ ⊆ (σ.image Prod.fst).cylinderStaircase k := by
  have hne : σ.Nonempty := Finset.image_nonempty.mp (K.isRelLowerSet_faces
    (image_fst_mem_of_mem_orderedCylinder hσ)).1
  have hchain := isChain_of_mem_orderedCylinder hσ
  have hfst {p : α × Fin 2} (hp : p ∈ σ) : p.1 ∈ σ.image Prod.fst := Finset.mem_image_of_mem _ hp
  -- Switch at the largest vertex on the initial end, or at the smallest vertex if that end
  -- is not met.
  by_cases h0 : (σ.filter (·.2 = 0)).Nonempty
  · obtain ⟨p, hp, hmax⟩ := (σ.filter (·.2 = 0)).exists_max_image Prod.fst h0
    obtain ⟨hpσ, hp0⟩ := Finset.mem_filter.mp hp
    refine ⟨p.1, hfst hpσ, fun q hq => Finset.mem_cylinderStaircase.mpr ⟨hfst hq, ?_⟩⟩
    rcases Fin.exists_fin_two.mp ⟨q.2, rfl⟩ with hq2 | hq2
    · exact Or.inl ⟨hq2, hmax q (Finset.mem_filter.mpr ⟨hq, hq2⟩)⟩
    · refine Or.inr ⟨hq2, ?_⟩
      rcases eq_or_ne p q with rfl | hpq
      · exact absurd (hp0.symm.trans hq2) (by decide)
      rcases hchain hpσ hq hpq with hle | hle
      · exact hle.1
      · exact absurd (hq2 ▸ hp0 ▸ hle.2) (by decide)
  · obtain ⟨p, hp, hmin⟩ := σ.exists_min_image Prod.fst hne
    refine ⟨p.1, hfst hp, fun q hq => Finset.mem_cylinderStaircase.mpr
      ⟨hfst hq, Or.inr ⟨?_, hmin q hq⟩⟩⟩
    rcases Fin.exists_fin_two.mp ⟨q.2, rfl⟩ with hq2 | hq2
    · exact absurd ⟨q, Finset.mem_filter.mpr ⟨hq, hq2⟩⟩ h0
    · exact hq2

/-- The faces of the ordered cylinder are exactly the nonempty subsets of the staircases over
faces of the base. -/
theorem mem_orderedCylinder_iff_exists_subset_cylinderStaircase {σ : Finset (α × Fin 2)} :
    σ ∈ K.orderedCylinder ↔ σ.Nonempty ∧ ∃ V ∈ K, ∃ k ∈ V, σ ⊆ V.cylinderStaircase k := by
  refine ⟨fun hσ => ⟨Finset.image_nonempty.mp (K.isRelLowerSet_faces
    (image_fst_mem_of_mem_orderedCylinder hσ)).1, _,
      image_fst_mem_of_mem_orderedCylinder hσ,
      exists_subset_cylinderStaircase_of_mem_orderedCylinder hσ⟩, ?_⟩
  rintro ⟨hne, V, hV, k, hk, hσ⟩
  exact (K.orderedCylinder.isRelLowerSet_faces
    (cylinderStaircase_mem_orderedCylinder hV hk)).2 hσ hne

/-- The ordered cylinder of a cone whose apex bounds every vertex of the complex is a cone with
apex the pair of that vertex and the terminal endpoint of the interval. -/
theorem isCone_orderedCylinder_of_isCone {v : α}
    (hK : PreAbstractSimplicialComplex.IsCone K.toPreAbstractSimplicialComplex v)
    (hv : ∀ w, ({w} : Finset α) ∈ K → w ≤ v) :
    PreAbstractSimplicialComplex.IsCone
      K.orderedCylinder.toPreAbstractSimplicialComplex (v, (1 : Fin 2)) := by
  refine ⟨K.orderedCylinder.singleton_mem _, ?_⟩
  intro σ hσ
  rw [orderedCylinder_toPreAbstractSimplicialComplex] at hσ ⊢
  rw [PreAbstractSimplicialComplex.mem_orderedProd_iff] at hσ ⊢
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Finset.image_insert, Prod.fst] using hK.insert_mem hσ.1
  · exact Finset.image_nonempty.mpr (Finset.insert_nonempty _ _)
  · rw [Finset.coe_insert]
    exact hσ.2.2.insert fun p _ _ ↦
      Or.inr ⟨hv p.1 (K.singleton_mem p.1), Fin.le_last p.2⟩

variable [OrderTop α]

/-- The ordered cylinder of the full abstract simplex is a cone with apex the greatest vertex at
the terminal endpoint of the interval. -/
theorem isCone_orderedCylinder_top :
    PreAbstractSimplicialComplex.IsCone
      (orderedCylinder (⊤ : AbstractSimplicialComplex α)).toPreAbstractSimplicialComplex
      (⊤, (1 : Fin 2)) := by
  apply isCone_orderedCylinder_of_isCone
  · exact ⟨Finset.singleton_nonempty _, fun _ _ ↦ Finset.insert_nonempty _ _⟩
  · exact fun _ _ ↦ le_top

end OrderedProd

section EndpointInclusions

variable [LinearOrder α]
variable {K : AbstractSimplicialComplex α}

/-- The zero-end copy of a complex is a simplicial subcomplex of its ordered cylinder. -/
theorem map_prodMk_zero_le_orderedCylinder (K : AbstractSimplicialComplex α) :
    K.toPreAbstractSimplicialComplex.map (fun a => (a, (0 : Fin 2))) ≤
      (orderedCylinder K).toPreAbstractSimplicialComplex := by
  rw [orderedCylinder, orderedProd_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.SimplicialMap.map_prodMkLeft_le_orderedProd
    K.toPreAbstractSimplicialComplex
    (⊤ : AbstractSimplicialComplex (Fin 2)).toPreAbstractSimplicialComplex 0
    ((⊤ : AbstractSimplicialComplex (Fin 2)).singleton_mem 0)

/-- The one-end copy of a complex is a simplicial subcomplex of its ordered cylinder. -/
theorem map_prodMk_one_le_orderedCylinder (K : AbstractSimplicialComplex α) :
    K.toPreAbstractSimplicialComplex.map (fun a => (a, (1 : Fin 2))) ≤
      (orderedCylinder K).toPreAbstractSimplicialComplex := by
  rw [orderedCylinder, orderedProd_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.SimplicialMap.map_prodMkLeft_le_orderedProd
    K.toPreAbstractSimplicialComplex
    (⊤ : AbstractSimplicialComplex (Fin 2)).toPreAbstractSimplicialComplex 1
    ((⊤ : AbstractSimplicialComplex (Fin 2)).singleton_mem 1)

/-- The bundled simplicial inclusion of the zero endpoint into an ordered cylinder. -/
def orderedCylinderZero (K : AbstractSimplicialComplex α) :
    PreAbstractSimplicialComplex.SimplicialMap K.toPreAbstractSimplicialComplex
      (orderedCylinder K).toPreAbstractSimplicialComplex :=
  PreAbstractSimplicialComplex.SimplicialMap.ofMapLE (fun a => (a, (0 : Fin 2)))
    (map_prodMk_zero_le_orderedCylinder K)

@[simp]
theorem coe_orderedCylinderZero (K : AbstractSimplicialComplex α) :
    ⇑(orderedCylinderZero K) = fun a => (a, (0 : Fin 2)) := by
  simp only [orderedCylinderZero,
    PreAbstractSimplicialComplex.SimplicialMap.coe_ofMapLE]

@[simp]
theorem orderedCylinderZero_apply (K : AbstractSimplicialComplex α) (a : α) :
    orderedCylinderZero K a = (a, (0 : Fin 2)) :=
  congrFun (coe_orderedCylinderZero K) a

/-- The bundled simplicial inclusion of the one endpoint into an ordered cylinder. -/
def orderedCylinderOne (K : AbstractSimplicialComplex α) :
    PreAbstractSimplicialComplex.SimplicialMap K.toPreAbstractSimplicialComplex
      (orderedCylinder K).toPreAbstractSimplicialComplex :=
  PreAbstractSimplicialComplex.SimplicialMap.ofMapLE (fun a => (a, (1 : Fin 2)))
    (map_prodMk_one_le_orderedCylinder K)

@[simp]
theorem coe_orderedCylinderOne (K : AbstractSimplicialComplex α) :
    ⇑(orderedCylinderOne K) = fun a => (a, (1 : Fin 2)) := by
  simp only [orderedCylinderOne,
    PreAbstractSimplicialComplex.SimplicialMap.coe_ofMapLE]

@[simp]
theorem orderedCylinderOne_apply (K : AbstractSimplicialComplex α) (a : α) :
    orderedCylinderOne K a = (a, (1 : Fin 2)) :=
  congrFun (coe_orderedCylinderOne K) a

end EndpointInclusions

/-! The following three computations pin down the staircase convention on the square. The two
monotone triangles are faces, while the pair of incomparable off-diagonal vertices is not. -/

/-- The `fst ≤ snd` triangle is a face of the ordered square. -/
theorem fstLeSndTriangle_mem_orderedProd_finTwo :
    ({((0 : Fin 2), (0 : Fin 2)), (0, 1), (1, 1)} : Finset (Fin 2 × Fin 2)) ∈
      orderedProd (⊤ : AbstractSimplicialComplex (Fin 2)) ⊤ := by
  rw [mem_orderedProd_iff]
  have htop : ({(0 : Fin 2), 1} : Finset (Fin 2)) ∈
      (⊤ : AbstractSimplicialComplex (Fin 2)) := by
    rw [← mem_toPreAbstractSimplicialComplex,
      _root_.AbstractSimplicialComplex.top_toPreAbstractSimplicialComplex]
    exact Finset.insert_nonempty 0 {1}
  refine ⟨by simpa using htop, by simpa using htop, ?_⟩
  simp [IsChain, Set.pairwise_insert]

/-- The `snd ≤ fst` triangle is a face of the ordered square. -/
theorem sndLeFstTriangle_mem_orderedProd_finTwo :
    ({((0 : Fin 2), (0 : Fin 2)), (1, 0), (1, 1)} : Finset (Fin 2 × Fin 2)) ∈
      orderedProd (⊤ : AbstractSimplicialComplex (Fin 2)) ⊤ := by
  rw [mem_orderedProd_iff]
  have htop : ({(0 : Fin 2), 1} : Finset (Fin 2)) ∈
      (⊤ : AbstractSimplicialComplex (Fin 2)) := by
    rw [← mem_toPreAbstractSimplicialComplex,
      _root_.AbstractSimplicialComplex.top_toPreAbstractSimplicialComplex]
    exact Finset.insert_nonempty 0 {1}
  refine ⟨by simpa using htop, by simpa using htop, ?_⟩
  simp [IsChain, Set.pairwise_insert]

/-- The incomparable off-diagonal vertices do not form a face of the ordered square. -/
theorem offDiagonalPair_notMem_orderedProd_finTwo :
    ({((0 : Fin 2), (1 : Fin 2)), (1, 0)} : Finset (Fin 2 × Fin 2)) ∉
      orderedProd (⊤ : AbstractSimplicialComplex (Fin 2)) ⊤ := by
  rw [mem_orderedProd_iff]
  rintro ⟨_, _, hchain⟩
  simp [IsChain, Set.pairwise_insert] at hchain

end AbstractSimplicialComplex
