/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public import TauCeti.Logic.Equiv.Set

import TauCeti.Topology.Closure

/-!
# Generic points and generizations

In a sober space, the generic points of irreducible components are precisely the points
with no proper generization. Every point of a closed subset is a specialization of such a
generic point of that subset, which has no proper generization in the subset
(`IsClosed.exists_maximal_specializes`). These facts let one choose component-generic points
without Noetherianity or a dimension argument. In a Noetherian space, every dense open set contains
all the component-generic points.

In a quasi-sober space where the closure of every component-generic point has nonempty
interior, a generization-stable subset is dense exactly when it contains all component-generic
points.

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

variable {X : Type*} [TopologicalSpace X]

/-- A generization of a component-generic point has the same closure as that point. -/
theorem Specializes.closure_eq_of_mem_genericPoints {x y : X}
    (hy : y ⤳ x) (hx : x ∈ genericPoints X) : _root_.closure {y} = _root_.closure {x} :=
  (hx.2 isIrreducible_singleton.closure hy.closure_subset).antisymm hy.closure_subset

namespace TauCeti

variable [QuasiSober X] [T0Space X]

/-- In a sober space, the generic points of irreducible components are exactly the points
with no proper generization. -/
theorem mem_genericPoints_iff {x : X} :
    x ∈ genericPoints X ↔ ∀ y : X, y ⤳ x → y = x := by
  constructor
  · intro hx y hy
    exact (inseparable_iff_closure_eq.mpr
      (hy.closure_eq_of_mem_genericPoints hx)).eq
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

/-- The component-generic points are stable under generization. -/
theorem TauCeti.stableUnderGeneralization_genericPoints {X : Type*} [TopologicalSpace X] :
    StableUnderGeneralization (genericPoints X) := by
  intro x y hyx hx
  rw [genericPoints, mem_ofPred_eq,
    hyx.closure_eq_of_mem_genericPoints hx]
  exact hx

/-- If every component-generic point has closure with nonempty interior, a dense set stable
under generization contains every component-generic point. -/
theorem Dense.genericPoints_subset_of_nonempty_interior
    {X : Type*} [TopologicalSpace X] {s : Set X} (hd : Dense s)
    (hinterior : ∀ x ∈ genericPoints X, (interior (closure {x})).Nonempty)
    (hs : StableUnderGeneralization s) : genericPoints X ⊆ s :=
  fun x hx ↦ hd.mem_of_nonempty_interior_closure_singleton hs (hinterior x hx)

/-- In a quasi-sober space where each component-generic point has closure with nonempty
interior, a set stable under generization is dense exactly when it contains all
component-generic points. -/
theorem TauCeti.dense_iff_genericPoints_subset_of_nonempty_interior
    {X : Type*} [TopologicalSpace X] [QuasiSober X] {s : Set X}
    (hinterior : ∀ x ∈ genericPoints X, (interior (closure {x})).Nonempty)
    (hs : StableUnderGeneralization s) : Dense s ↔ genericPoints X ⊆ s :=
  ⟨fun hd ↦ hd.genericPoints_subset_of_nonempty_interior hinterior hs,
    fun h ↦ (dense_iff_closure_eq.mpr genericPoints.closure).mono h⟩

/-- Every point of a closed subset of a quasi-sober space is a specialization of a generic
point of an irreducible component of that subset. -/
theorem IsClosed.exists_genericPoint_specializes {X : Type*} [TopologicalSpace X]
    [QuasiSober X] {s : Set X} (hs : IsClosed s) {x : X} (hx : x ∈ s) :
    ∃ z : s, z ∈ genericPoints s ∧ (z : X) ⤳ x := by
  let : QuasiSober s := hs.isClosedEmbedding_subtypeVal.quasiSober
  let C : irreducibleComponents s :=
    ⟨irreducibleComponent (⟨x, hx⟩ : s), irreducibleComponent_mem_irreducibleComponents _⟩
  refine ⟨(genericPoints.ofComponent C).val, (genericPoints.ofComponent C).property, ?_⟩
  exact ((genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent).map
    continuous_subtypeVal

/-- Every point of a closed subset of a quasi-sober `T₀` space is a specialization of a point of
the subset with no proper generization in the subset, namely the generic point of an irreducible
component of the subset. -/
theorem IsClosed.exists_maximal_specializes {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [T0Space X] {s : Set X} (hs : IsClosed s) {x : X} (hx : x ∈ s) :
    ∃ z ∈ s, z ⤳ x ∧ ∀ y ∈ s, y ⤳ z → y = z := by
  let : QuasiSober s := hs.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨z, hz, hzx⟩ := hs.exists_genericPoint_specializes hx
  refine ⟨z, z.property, hzx, fun y hy hyz ↦ ?_⟩
  exact congrArg Subtype.val ((TauCeti.mem_genericPoints_iff.mp hz) ⟨y, hy⟩
    ((subtype_specializes_iff _ _).mpr hyz))

/-- In a Noetherian space, a dense open set contains the generic point of every irreducible
component. -/
theorem Dense.genericPoints_subset {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] {U : Set X} (hU : Dense U) (hUo : IsOpen U) :
    genericPoints X ⊆ U := by
  -- Each irreducible component contains a nonempty open set, which meets `U`.
  intro η hη
  obtain ⟨o, ho, hne, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hη
  obtain ⟨y, hyo, hyU⟩ := hU.inter_open_nonempty o ho hne
  exact (isGenericPoint_closure (x := η)).mem_open_set_iff hUo |>.mpr ⟨y, hoC hyo, hyU⟩

section Maps

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous generalizing map into a quasi-sober space sends component-generic points to
component-generic points. -/
theorem GeneralizingMap.mapsTo_genericPoints [QuasiSober Y] {f : X → Y}
    (hf : GeneralizingMap f) (hc : Continuous f) :
    MapsTo f (genericPoints X) (genericPoints Y) := by
  intro x hx
  refine ⟨isIrreducible_singleton.closure, fun Z hZ hxZ ↦ ?_⟩
  have hη := hZ.isGenericPoint_genericPoint_closure
  obtain ⟨x', hx'x, hx'⟩ := hf (hη.specializes
    (subset_closure (hxZ (subset_closure (mem_singleton _)))))
  have hxx' : x ⤳ x' := specializes_iff_closure_subset.mpr
    (hx'x.closure_eq_of_mem_genericPoints hx).le
  have hfx : f x ⤳ hZ.genericPoint := hx' ▸ hxx'.map hc
  exact subset_closure.trans (hη.def ▸ hfx.closure_subset)

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
theorem GeneralizingMap.invOn_preimage_closure_image_irreducibleComponents
    [QuasiSober Y] {f : X → Y}
    (hf : GeneralizingMap f)
    (h : BijOn (fun Z ↦ closure (f '' Z)) (irreducibleComponents X)
      (irreducibleComponents Y)) :
    InvOn (f ⁻¹' ·) (fun Z ↦ closure (f '' Z))
      (irreducibleComponents X) (irreducibleComponents Y) := by
  have key : LeftInvOn (f ⁻¹' ·) (fun Z ↦ closure (f '' Z))
      (irreducibleComponents X) := by
    intro Z hZ
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
  exact ⟨key, h.surjOn.leftInvOn_of_rightInvOn key⟩

/-- For a generalizing map into a quasi-sober space, a closure-of-image bijection on
irreducible components induces a preimage bijection in the opposite direction. -/
theorem GeneralizingMap.bijOn_preimage_irreducibleComponents [QuasiSober Y] {f : X → Y}
    (hf : GeneralizingMap f)
    (h : BijOn (fun Z ↦ closure (f '' Z)) (irreducibleComponents X)
      (irreducibleComponents Y)) :
    BijOn (f ⁻¹' ·) (irreducibleComponents Y) (irreducibleComponents X) :=
  h.symm (hf.invOn_preimage_closure_image_irreducibleComponents h).symm

end Maps
