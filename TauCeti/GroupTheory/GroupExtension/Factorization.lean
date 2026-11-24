/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Ordered factorization across a central kernel

Suppose three subgroups of `G` have images under `f : G →* H` whose ordered product gives
unique factorizations in `H`. If `f` has central kernel, the three subgroups give unique
factorizations in `G` exactly when their intersections with the kernel give unique factorizations
there. This allows induction on central truncations: the quotient determines the images of the
factors, and the kernel accounts for the remaining freedom.

The application to sign subgroups of a graded nilpotent group is the induction step in
T. Bridgeland, *Scattering diagrams, Hall algebras and stability conditions*, §3
(arXiv:1603.00416).
-/

public section

namespace MonoidHom

variable {G H : Type*} [Group G] [Group H]

section

variable (f : G →* H) (A B C : Subgroup G)

private def orderedMul (x : A × B × C) : G := (x.1 : G) * x.2.1 * x.2.2

private abbrev KernelFactors := A.subgroupOf f.ker × B.subgroupOf f.ker × C.subgroupOf f.ker

private def ofKernel (x : KernelFactors f A B C) : A × B × C :=
  (⟨x.1, x.1.property⟩, ⟨x.2.1, x.2.1.property⟩, ⟨x.2.2, x.2.2.property⟩)

private def mapFactors : A × B × C →* A.map f × B.map f × C.map f :=
  (f.subgroupMap A).prodMap ((f.subgroupMap B).prodMap (f.subgroupMap C))

private theorem mapFactors_surjective : Function.Surjective (mapFactors f A B C) :=
  (f.subgroupMap_surjective A).prodMap
    ((f.subgroupMap_surjective B).prodMap (f.subgroupMap_surjective C))

private theorem orderedMul_mapFactors (x : A × B × C) :
    orderedMul (A.map f) (B.map f) (C.map f) (mapFactors f A B C x) =
      f (orderedMul A B C x) := by
  -- Reduce the nested product and subgroup maps to their ambient group coordinates.
  change f (x.1 : G) * f (x.2.1 : G) * f (x.2.2 : G) = f ((x.1 : G) * x.2.1 * x.2.2)
  simp only [map_mul]

-- Division takes place within each factor before using equality of the images.
private def divFactors (x y : A × B × C)
    (h : mapFactors f A B C x = mapFactors f A B C y) : KernelFactors f A B C :=
  (⟨⟨(x.1 : G) / y.1, f.div_mem_ker_iff.mpr (congrArg (fun p ↦ (p.1 : H)) h)⟩,
      A.div_mem x.1.property y.1.property⟩,
   ⟨⟨(x.2.1 : G) / y.2.1, f.div_mem_ker_iff.mpr (congrArg (fun p ↦ (p.2.1 : H)) h)⟩,
      B.div_mem x.2.1.property y.2.1.property⟩,
   ⟨⟨(x.2.2 : G) / y.2.2, f.div_mem_ker_iff.mpr (congrArg (fun p ↦ (p.2.2 : H)) h)⟩,
      C.div_mem x.2.2.property y.2.2.property⟩)

private theorem ofKernel_divFactors_mul (x y : A × B × C)
    (h : mapFactors f A B C x = mapFactors f A B C y) :
    ofKernel f A B C (divFactors f A B C x y h) * y = x := by
  ext <;> simp [ofKernel, divFactors]

-- Collect the central corrections on the left of the ordered product.
private theorem orderedMul_ofKernel_mul (hc : f.ker ≤ Subgroup.center G)
    (k : KernelFactors f A B C) (x : A × B × C) :
    orderedMul A B C (ofKernel f A B C k * x) =
      ((orderedMul (A.subgroupOf f.ker) (B.subgroupOf f.ker) (C.subgroupOf f.ker) k : f.ker) : G) *
        orderedMul A B C x := by
  have hb : Commute (x.1 : G) (k.2.1 : f.ker).val :=
    Subgroup.mem_center_iff.mp (hc (k.2.1 : f.ker).property) _
  have hd : Commute ((x.1 : G) * x.2.1) (k.2.2 : f.ker).val :=
    Subgroup.mem_center_iff.mp (hc (k.2.2 : f.ker).property) _
  simp only [orderedMul, ofKernel, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
  rw [hb.mul_mul_mul_comm, hd.mul_mul_mul_comm]

private theorem bijective_kernel_of_bijective_orderedMul
    (himage : Function.Injective (orderedMul (A.map f) (B.map f) (C.map f)))
    (h : Function.Bijective (orderedMul A B C)) :
    Function.Bijective (orderedMul (A.subgroupOf f.ker) (B.subgroupOf f.ker)
      (C.subgroupOf f.ker)) := by
  constructor
  · intro k l hkl
    have he := h.1 (a₁ := ofKernel f A B C k) (a₂ := ofKernel f A B C l)
      (congrArg Subtype.val hkl)
    ext
    · exact congrArg (fun x ↦ (x.1 : G)) he
    · exact congrArg (fun x ↦ (x.2.1 : G)) he
    · exact congrArg (fun x ↦ (x.2.2 : G)) he
  · intro k
    obtain ⟨x, hx⟩ := h.2 (k : G)
    have he : mapFactors f A B C x = mapFactors f A B C 1 := by
      apply himage
      rw [orderedMul_mapFactors, hx, orderedMul_mapFactors]
      simp [orderedMul, MonoidHom.mem_ker.mp k.property]
    refine ⟨divFactors f A B C x 1 he, Subtype.ext ?_⟩
    simp only [orderedMul, divFactors, Subgroup.coe_mul, Prod.fst_one, Prod.snd_one,
      Subgroup.coe_one, div_one]
    exact hx

private theorem bijective_orderedMul_of_bijective_kernel
    (hc : f.ker ≤ Subgroup.center G)
    (himage : Function.Bijective (orderedMul (A.map f) (B.map f) (C.map f)))
    (hk : Function.Bijective (orderedMul (A.subgroupOf f.ker) (B.subgroupOf f.ker)
      (C.subgroupOf f.ker))) : Function.Bijective (orderedMul A B C) := by
  constructor
  · intro x y hxy
    have he : mapFactors f A B C x = mapFactors f A B C y :=
      himage.1 (by simp only [orderedMul_mapFactors, hxy])
    let k := divFactors f A B C x y he
    have hky : ofKernel f A B C k * y = x := ofKernel_divFactors_mul f A B C x y he
    have hk1 : orderedMul (A.subgroupOf f.ker) (B.subgroupOf f.ker) (C.subgroupOf f.ker) k =
        orderedMul (A.subgroupOf f.ker) (B.subgroupOf f.ker) (C.subgroupOf f.ker) 1 := by
      apply Subtype.ext
      have hm := orderedMul_ofKernel_mul f A B C hc k y
      rw [hky, hxy] at hm
      simp only [orderedMul, Prod.fst_one, Prod.snd_one, Subgroup.coe_one, one_mul]
      exact mul_right_cancel (hm.symm.trans (one_mul _).symm)
    rw [← hky, hk.1 hk1]
    simp [ofKernel]
  · intro g
    obtain ⟨q, hq⟩ := himage.2 (f g)
    obtain ⟨x, rfl⟩ := mapFactors_surjective f A B C q
    rw [orderedMul_mapFactors] at hq
    have hd : g / orderedMul A B C x ∈ f.ker := f.div_mem_ker_iff.mpr hq.symm
    obtain ⟨k, hkg⟩ := hk.2 ⟨g / orderedMul A B C x, hd⟩
    refine ⟨ofKernel f A B C k * x, ?_⟩
    rw [orderedMul_ofKernel_mul f A B C hc k x, congrArg Subtype.val hkg]
    exact div_mul_cancel g _

/-- If the images of three subgroups under `f` multiply bijectively onto the codomain and
`f` has central kernel, the original subgroups multiply bijectively onto the domain exactly
when their intersections with the kernel multiply bijectively onto the kernel.
The ordered products are `a * b * c`; the subgroups need not be normal or commute. -/
theorem bijective_mul_mul_iff_of_ker_le_center
    (hc : f.ker ≤ Subgroup.center G)
    (himage : Function.Bijective
      (fun (x : A.map f × B.map f × C.map f) ↦ (x.1 : H) * x.2.1 * x.2.2)) :
    Function.Bijective (fun (x : A × B × C) ↦ (x.1 : G) * x.2.1 * x.2.2) ↔
      Function.Bijective (fun (x : A.subgroupOf f.ker × B.subgroupOf f.ker × C.subgroupOf f.ker) ↦
        (x.1 : f.ker) * x.2.1 * x.2.2) :=
  ⟨bijective_kernel_of_bijective_orderedMul f A B C himage.1,
    bijective_orderedMul_of_bijective_kernel f A B C hc himage⟩

end

end MonoidHom
