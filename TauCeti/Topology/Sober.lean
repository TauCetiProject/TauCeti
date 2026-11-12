/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sober

/-!
# Generic points and generizations

In a sober space, the generic points of irreducible components are precisely the points
with no proper generization. Every point of a closed subset is a specialization of such a
generic point of that subset. These facts let one choose component-generic points without
Noetherianity or a dimension argument.

Bijections on component-generic points are equivalent to bijections on irreducible components
by closure of image. They can be checked on an open cover of the target and its inverse-image
cover of the source; this permits component labels obtained on affine charts to be glued.
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
  [QuasiSober X] [T0Space X] [QuasiSober Y] [T0Space Y]

/-- An open embedding identifies component-generic points with those of the ambient space
that lie in its range. -/
@[simp]
theorem Topology.IsOpenEmbedding.mem_genericPoints_iff {j : X → Y}
    (hj : IsOpenEmbedding j) (x : X) :
    j x ∈ genericPoints Y ↔ x ∈ genericPoints X := by
  rw [TauCeti.mem_genericPoints_iff, TauCeti.mem_genericPoints_iff]
  constructor
  · intro hx z hz
    exact hj.injective (hx (j z) (hz.map hj.continuous))
  · intro hx y hy
    obtain ⟨z, rfl⟩ := hy.mem_open hj.isOpen_range ⟨x, rfl⟩
    exact congrArg j (hx z (hj.isEmbedding.isInducing.specializes_iff.mp hy))

/-- For a continuous map between sober spaces, bijectivity on component-generic points is
equivalent to bijectivity on irreducible components by closure of image. -/
theorem Continuous.bijOn_genericPoints_iff {f : X → Y} (hf : Continuous f) :
    Set.BijOn f (genericPoints X) (genericPoints Y) ↔
      Set.BijOn (fun Z ↦ closure (f '' Z)) (irreducibleComponents X)
        (irreducibleComponents Y) := by
  have himage (x : X) : closure (f '' closure {x}) = closure {f x} :=
    (isGenericPoint_closure.image hf).def.symm
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro Z hZ
      let x := genericPoints.ofComponent ⟨Z, hZ⟩
      have hx : closure {x.1} = Z := (genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩).def
      dsimp only
      rw [← hx, himage]
      exact h.mapsTo x.2
    · intro Z hZ W hW heq
      let x := genericPoints.ofComponent ⟨Z, hZ⟩
      let y := genericPoints.ofComponent ⟨W, hW⟩
      have hx := genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩
      have hy := genericPoints.isGenericPoint_ofComponent ⟨W, hW⟩
      have hxy : f x.1 = f y.1 := (hx.image hf).eq (by
        dsimp only at heq ⊢
        rw [heq]
        exact hy.image hf)
      exact hx.def.symm.trans ((congrArg (fun z : X ↦ closure {z})
        (h.injOn x.2 y.2 hxy)).trans hy.def)
    · intro Z hZ
      let y := genericPoints.ofComponent ⟨Z, hZ⟩
      obtain ⟨x, hx, hxy⟩ := h.surjOn y.2
      refine ⟨closure {x}, hx, ?_⟩
      dsimp only
      rw [himage, hxy]
      exact (genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩).def
  · intro h
    refine ⟨fun x hx ↦ ?_, fun x hx y hy hxy ↦ ?_, fun y hy ↦ ?_⟩
    · have := h.mapsTo hx
      rwa [himage] at this
    · have heq : closure {x} = closure {y} := h.injOn hx hy (by rw [himage, himage, hxy])
      exact isGenericPoint_closure.eq (heq ▸ isGenericPoint_closure)
    · obtain ⟨Z, hZ, heq⟩ := h.surjOn hy
      let x := genericPoints.ofComponent ⟨Z, hZ⟩
      have hx := genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩
      refine ⟨x.1, x.2, (hx.image hf).eq ?_⟩
      dsimp only at heq ⊢
      rw [heq]
      exact isGenericPoint_closure

/-- Bijections on component-generic points glue across an open cover of the target and its
inverse-image cover of the source. The squares need only commute on underlying points. -/
theorem TauCeti.bijOn_genericPoints_of_openCover
    {ι : Type*} {U V : ι → Type*}
    [∀ i, TopologicalSpace (U i)] [∀ i, TopologicalSpace (V i)]
    [∀ i, QuasiSober (U i)] [∀ i, T0Space (U i)]
    [∀ i, QuasiSober (V i)] [∀ i, T0Space (V i)]
    {f : X → Y} {j : ∀ i, U i → X} {k : ∀ i, V i → Y} {g : ∀ i, U i → V i}
    (hj : ∀ i, IsOpenEmbedding (j i)) (hk : ∀ i, IsOpenEmbedding (k i))
    (hcover : ∀ y, ∃ i, y ∈ range (k i))
    (hrange : ∀ i, range (j i) = f ⁻¹' range (k i))
    (hcomm : ∀ i x, f (j i x) = k i (g i x))
    (h : ∀ i, BijOn (g i) (genericPoints (U i)) (genericPoints (V i))) :
    BijOn f (genericPoints X) (genericPoints Y) := by
  have hlift (x : X) (i : ι) (hx : f x ∈ range (k i)) : x ∈ range (j i) := by
    rw [hrange]
    exact hx
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := hcover (f x)
    obtain ⟨z, rfl⟩ := hlift x i hi
    rw [hcomm]
    exact (hk i).mem_genericPoints_iff _ |>.mpr
      ((h i).mapsTo ((hj i).mem_genericPoints_iff _ |>.mp hx))
  · intro x hx y hy hxy
    obtain ⟨i, hi⟩ := hcover (f x)
    obtain ⟨z, rfl⟩ := hlift x i hi
    obtain ⟨w, rfl⟩ := hlift y i (hxy ▸ hi)
    have hzw : g i z = g i w := (hk i).injective (by simpa only [hcomm] using hxy)
    exact congrArg (j i) ((h i).injOn
      ((hj i).mem_genericPoints_iff _ |>.mp hx)
      ((hj i).mem_genericPoints_iff _ |>.mp hy) hzw)
  · intro y hy
    obtain ⟨i, z, rfl⟩ := hcover y
    obtain ⟨w, hw, hwz⟩ := (h i).surjOn ((hk i).mem_genericPoints_iff _ |>.mp hy)
    exact ⟨j i w, (hj i).mem_genericPoints_iff _ |>.mpr hw, by rw [hcomm, hwz]⟩

end Maps
