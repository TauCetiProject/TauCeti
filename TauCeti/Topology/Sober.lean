/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sober
public import TauCeti.Logic.Equiv.Set

/-!
# Generic points and generizations

In a sober space, the generic points of irreducible components are precisely the points
with no proper generization. Every point of a closed subset is a specialization of such a
generic point of that subset. These facts let one choose component-generic points without
Noetherianity or a dimension argument.

In a sober space, `x ↦ closure {x}` is a bijection from component-generic points onto
irreducible components. For a continuous map between sober spaces, bijections on
component-generic points are therefore equivalent to bijections on irreducible components by
closure of image. Bijections on component-generic points restrict along open embeddings, and
can be checked on an open cover of the target and its inverse-image cover of the source; this
permits component labels obtained on affine charts to be glued. For a generalizing map, such as a
flat morphism of schemes, a bijection on irreducible components by closure of image is inverted by
taking preimages.
-/

public section

open Set Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]

/-- In a sober space, the generic points of irreducible components are exactly the points
with no proper generization. -/
theorem mem_genericPoints_iff {x : X} :
    x ∈ genericPoints X ↔ ∀ y : X, y ⤳ x → y = x := by
  constructor
  · intro hx y hy
    have hle : closure ({x} : Set X) ⊆ closure {y} :=
      specializes_iff_closure_subset.mp hy
    exact (hy.antisymm (specializes_iff_closure_subset.mpr
      (hx.2 isIrreducible_singleton.closure hle))).eq
  · intro hx
    refine ⟨isIrreducible_singleton.closure, fun t ht hxt ↦ ?_⟩
    have hgen := ht.isGenericPoint_genericPoint_closure
    have hxmem : x ∈ t := hxt (subset_closure (mem_singleton x))
    have heq : ht.genericPoint = x := hx _ (hgen.specializes (subset_closure hxmem))
    calc
      t ⊆ closure t := subset_closure
      _ = closure {ht.genericPoint} := hgen.def.symm
      _ = closure {x} := by rw [heq]

/-- In a sober space, `x ↦ closure {x}` maps the component-generic points bijectively onto the
irreducible components. -/
theorem bijOn_closure_singleton_genericPoints :
    BijOn (fun x : X ↦ closure {x}) (genericPoints X) (irreducibleComponents X) :=
  Equiv.bijOn_of_coe_eq genericPoints.equiv fun z ↦ by
    rw [genericPoints.equiv_apply]
    exact (genericPoints.isGenericPoint z).def.symm

end TauCeti

/-- Every point of a closed subset of a quasi-sober space is a specialization of a generic
point of an irreducible component of that subset. -/
theorem IsClosed.exists_genericPoint_specializes {X : Type*} [TopologicalSpace X]
    [QuasiSober X] {s : Set X} (hs : IsClosed s) {x : X} (hx : x ∈ s) :
    ∃ z : s, z ∈ genericPoints s ∧ (z : X) ⤳ x := by
  let : QuasiSober s := hs.isClosedEmbedding_subtypeVal.quasiSober
  let C : irreducibleComponents s :=
    ⟨irreducibleComponent (⟨x, hx⟩ : s), irreducibleComponent_mem_irreducibleComponents _⟩
  refine ⟨(genericPoints.ofComponent C).1, (genericPoints.ofComponent C).2, ?_⟩
  exact ((genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent).map
    continuous_subtype_val

section Maps

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A point is component-generic if and only if its image under an open embedding is
component-generic in the ambient space. -/
@[simp]
theorem Topology.IsOpenEmbedding.mem_genericPoints_iff {j : X → Y}
    (hj : IsOpenEmbedding j) (x : X) :
    j x ∈ genericPoints Y ↔ x ∈ genericPoints X := by
  simp only [genericPoints, mem_ofPred_eq]
  have hcl : closure {x} = j ⁻¹' closure {j x} := by
    rw [hj.isEmbedding.closure_eq_preimage_closure_image, image_singleton]
  constructor
  · intro hx
    rw [hcl]
    exact preimage_mem_irreducibleComponents hx hj
      ⟨j x, subset_closure (mem_singleton _), ⟨x, rfl⟩⟩
  · intro hx
    refine ⟨isIrreducible_singleton.closure, fun Z hZ hxZ ↦ ?_⟩
    have hnonempty : (Z ∩ range j).Nonempty :=
      ⟨j x, hxZ (subset_closure (mem_singleton _)), ⟨x, rfl⟩⟩
    have hpre : j ⁻¹' Z ⊆ closure {x} := hx.2 (hZ.preimage hj hnonempty) (by
      rw [hcl]
      exact preimage_mono hxZ)
    refine (subset_closure_inter_of_isPreirreducible_of_isOpen hZ.2
      hj.isOpen_range hnonempty).trans (closure_minimal ?_ isClosed_closure)
    rintro y ⟨hy, z, rfl⟩
    have hz := hpre hy
    rwa [hcl] at hz

/-- For a continuous map between sober spaces, bijectivity on component-generic points is
equivalent to bijectivity on irreducible components by closure of image. -/
theorem Continuous.bijOn_genericPoints_iff
    [QuasiSober X] [T0Space X] [QuasiSober Y] [T0Space Y]
    {f : X → Y} (hf : Continuous f) :
    Set.BijOn f (genericPoints X) (genericPoints Y) ↔
      Set.BijOn (fun Z ↦ closure (f '' Z)) (irreducibleComponents X)
        (irreducibleComponents Y) := by
  have hcX := TauCeti.bijOn_closure_singleton_genericPoints (X := X)
  have hcY := TauCeti.bijOn_closure_singleton_genericPoints (X := Y)
  have hcomp : (fun Z ↦ closure (f '' Z)) ∘ (fun x : X ↦ closure {x}) =
      (fun y : Y ↦ closure {y}) ∘ f := funext fun x ↦ by
    simp only [Function.comp_apply]
    exact (isGenericPoint_closure.image hf).def.symm
  rw [← hcX.image_eq, ← bijOn_comp_iff hcX.injOn, hcomp]
  constructor
  · exact hcY.comp
  · intro h
    have hmaps : MapsTo f (genericPoints X) (genericPoints Y) := fun x hx ↦ by
      simpa only [genericPoints, mem_ofPred_eq, Function.comp_apply] using h.mapsTo hx
    refine ⟨hmaps, h.injOn.of_comp, fun y hy ↦ ?_⟩
    obtain ⟨x, hx, hxy⟩ := h.surjOn (hcY.mapsTo hy)
    exact ⟨x, hx, hcY.injOn (hmaps hx) hy hxy⟩

/-- Bijections on component-generic points restrict along open embeddings: if `f` is bijective
on component-generic points, `f (j x) = k (g x)` for open embeddings `j` and `k`, and
`f ⁻¹' range k ⊆ range j`, then `g` is bijective on component-generic points. The maps `f`
and `g` need not be continuous. -/
theorem TauCeti.bijOn_genericPoints_of_isOpenEmbedding
    {U V : Type*} [TopologicalSpace U] [TopologicalSpace V]
    {f : X → Y} {j : U → X} {k : V → Y} {g : U → V}
    (hj : IsOpenEmbedding j) (hk : IsOpenEmbedding k)
    (hrange : f ⁻¹' range k ⊆ range j) (hcomm : ∀ x, f (j x) = k (g x))
    (h : BijOn f (genericPoints X) (genericPoints Y)) :
    BijOn g (genericPoints U) (genericPoints V) := by
  refine ⟨fun x hx ↦ ?_, fun x hx y hy hxy ↦ ?_, fun v hv ↦ ?_⟩
  · rw [← hk.mem_genericPoints_iff, ← hcomm]
    exact h.mapsTo ((hj.mem_genericPoints_iff x).mpr hx)
  · refine hj.injective (h.injOn ((hj.mem_genericPoints_iff x).mpr hx)
      ((hj.mem_genericPoints_iff y).mpr hy) ?_)
    rw [hcomm, hcomm, hxy]
  · obtain ⟨x, hx, hxv⟩ := h.surjOn ((hk.mem_genericPoints_iff v).mpr hv)
    obtain ⟨u, rfl⟩ := hrange ⟨v, hxv.symm⟩
    refine ⟨u, (hj.mem_genericPoints_iff u).mp hx, hk.injective ?_⟩
    rw [← hcomm, hxv]

/-- A map is bijective on component-generic points exactly when it is so on every chart of an
open cover of the target and its inverse-image cover of the source. The maps `f` and `g i` need
not be continuous, and commute with the open embeddings as `f (j i x) = k i (g i x)`. -/
theorem TauCeti.bijOn_genericPoints_iff_of_isOpenEmbedding
    {ι : Type*} {U V : ι → Type*}
    [∀ i, TopologicalSpace (U i)] [∀ i, TopologicalSpace (V i)]
    {f : X → Y} {j : ∀ i, U i → X} {k : ∀ i, V i → Y} {g : ∀ i, U i → V i}
    (hj : ∀ i, IsOpenEmbedding (j i)) (hk : ∀ i, IsOpenEmbedding (k i))
    (hcover : ∀ y, ∃ i, y ∈ range (k i))
    (hrange : ∀ i, f ⁻¹' range (k i) ⊆ range (j i))
    (hcomm : ∀ i x, f (j i x) = k i (g i x)) :
    BijOn f (genericPoints X) (genericPoints Y) ↔
      ∀ i, BijOn (g i) (genericPoints (U i)) (genericPoints (V i)) := by
  refine ⟨fun h i ↦ TauCeti.bijOn_genericPoints_of_isOpenEmbedding (hj i) (hk i) (hrange i)
    (hcomm i) h, fun h ↦ ⟨?_, ?_, ?_⟩⟩
  · intro x hx
    obtain ⟨i, hi⟩ := hcover (f x)
    obtain ⟨z, rfl⟩ := hrange i hi
    rw [hcomm]
    exact (hk i).mem_genericPoints_iff _ |>.mpr
      ((h i).mapsTo ((hj i).mem_genericPoints_iff _ |>.mp hx))
  · intro x hx y hy hxy
    obtain ⟨i, hi⟩ := hcover (f x)
    obtain ⟨z, rfl⟩ := hrange i hi
    obtain ⟨w, rfl⟩ := hrange i (show f y ∈ range (k i) from hxy ▸ hi)
    have hzw : g i z = g i w := (hk i).injective (by simpa only [hcomm] using hxy)
    exact congrArg (j i) ((h i).injOn
      ((hj i).mem_genericPoints_iff _ |>.mp hx)
      ((hj i).mem_genericPoints_iff _ |>.mp hy) hzw)
  · intro y hy
    obtain ⟨i, z, rfl⟩ := hcover y
    obtain ⟨w, hw, hwz⟩ := (h i).surjOn ((hk i).mem_genericPoints_iff _ |>.mp hy)
    exact ⟨j i w, (hj i).mem_genericPoints_iff _ |>.mpr hw, by rw [hcomm, hwz]⟩

/-- **Closure of image and preimage are inverse bijections on irreducible components.** Let
`f` be a generalizing map into a quasi-sober space, for example a flat morphism of
schemes, such that `Z ↦ closure (f '' Z)` maps the irreducible components of the source
bijectively onto those of the target. Then `W ↦ f ⁻¹' W` maps the irreducible components of the
target bijectively onto those of the source, inverting that bijection. -/
theorem GeneralizingMap.bijOn_preimage_irreducibleComponents [QuasiSober Y] {f : X → Y}
    (hf : GeneralizingMap f)
    (h : BijOn (fun Z ↦ closure (f '' Z)) (irreducibleComponents X)
      (irreducibleComponents Y)) :
    BijOn (f ⁻¹' ·) (irreducibleComponents Y) (irreducibleComponents X) := by
  have key {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : f ⁻¹' closure (f '' Z) = Z := by
    refine subset_antisymm (fun x hx ↦ ?_)
      ((subset_preimage_image f Z).trans (preimage_mono subset_closure))
    -- The generic point of the component `closure (f '' Z)` generalizes `f x`; lift it to a
    -- generalization `x'` of `x`, which lies on a component `Z'` with the same closed image.
    have hW := h.mapsTo hZ
    have hη := hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hW)
    obtain ⟨x', hx'x, hx'⟩ := hf (hη.specializes hx)
    obtain ⟨Z', hZ', hsub⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible (closure {x'})
        isIrreducible_singleton.closure
    have hle : closure (f '' Z) ⊆ closure (f '' Z') := by
      rw [← hη.def]
      exact closure_mono (singleton_subset_iff.mpr
        ⟨x', hsub (subset_closure (mem_singleton x')), hx'⟩)
    have hZZ' : Z' = Z := h.injOn hZ' hZ (subset_antisymm (hW.2 (h.mapsTo hZ').1 hle) hle)
    exact hZZ' ▸ hsub (specializes_iff_mem_closure.mp hx'x)
  refine ⟨fun W hW ↦ ?_, fun W hW W' hW' hWW' ↦ ?_, fun Z hZ ↦ ⟨_, h.mapsTo hZ, key hZ⟩⟩
  · obtain ⟨Z, hZ, rfl⟩ := h.surjOn hW
    simpa only [key hZ] using hZ
  · obtain ⟨Z, hZ, rfl⟩ := h.surjOn hW
    obtain ⟨Z', hZ', rfl⟩ := h.surjOn hW'
    simp only [key hZ, key hZ'] at hWW'
    rw [hWW']

end Maps
