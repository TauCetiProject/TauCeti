/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.LocalDegree
public import TauCeti.AlgebraicTopology.Singular.IntervalGenerator

/-!
# Incidence numbers of `1`-cells

The boundary sphere of a `1`-cell `j` is `S⁰ = {-e₀, e₀}`, and the standard generator of its reduced
homology is `[-e₀] - [e₀]` (`TauCeti.reducedSingularHomologyTopCatSphereIso_zero_inv_ι`). Hence
the cellular boundary of `j` is the difference of the `0`-cells at the two endpoints of its
attaching map: the incidence coefficient of a `0`-cell `i` is `1` if the endpoint `-e₀` is the
point of `i`, minus `1` if the endpoint `e₀` is (`TauCeti.cellularIncidence_zero`).

If the attaching map of `j` is injective, its two endpoints are distinct, so every `0`-cell in the
frontier of `j` has incidence number `1` or `-1`
(`TauCeti.isUnit_cellularIncidence_zero_of_injective`). This is the case of `0`-dimensional faces
left out of `TauCeti.isUnit_cellularIncidence_of_injective`, where the boundary sphere is
connected.

## Main results

* `TauCeti.cellularIncidence_zero`: the incidence numbers of a `1`-cell are differences of
  endpoint indicators.
* `TauCeti.isUnit_cellularIncidence_zero_of_injective`: injective attaching maps of `1`-cells have
  unit incidence numbers.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the cellular boundary formula in degree one.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D]

variable (R : Type w) [Ring R]

open scoped Classical in
/-- **The incidence numbers of a `1`-cell.** The incidence coefficient of a `0`-cell `i` in the
cellular boundary of a `1`-cell `j` counts the endpoint `-e₀` of the attaching map of `j` with
sign `+1` and the endpoint `e₀` with sign `-1`, whenever it is the point of `i`. -/
theorem cellularIncidence_zero (i : cell C 0) (j : cell C 1) :
    cellularIncidence C R 0 i j =
      (if ((cellAttachingMap j sphereMinus : skeletonObj C 1) : X) ∈ openCell 0 i then 1 else 0) -
        if ((cellAttachingMap j spherePlus : skeletonObj C 1) : X) ∈ openCell 0 i then 1
        else 0 := by
  -- Read the incidence coefficient as a local degree at a point `x` of `i`. In the local
  -- homology `H₀(X⁰, X⁰ ∖ {x})`, the class of `x` is the local class of `i`, and the class of any
  -- other point of the `0`-skeleton vanishes.
  obtain ⟨x₀, hx₀⟩ := openCell_nonempty 0 i
  let x : skeletonObj C 1 := ⟨x₀, openCell_subset_skeletonLT 0 i hx₀⟩
  have hx : (x : X) ∈ openCell 0 i := hx₀
  have hgen : (reducedSingularHomologyι (ModuleCat.of R R) 0).app (TopCat.diskBoundary.{w} 1)
      ((reducedSingularHomologyTopCatSphereIso (ModuleCat.of R R) 0).inv 1) =
        singularHomology₀Section (ModuleCat.of R R) sphereMinus 1 -
          singularHomology₀Section (ModuleCat.of R R) spherePlus 1 :=
    ConcreteCategory.congr_hom
      (reducedSingularHomologyTopCatSphereIso_zero_inv_ι (ModuleCat.of R R)) 1
  have hmap (p : TopCat.diskBoundary.{w} 1) := ConcreteCategory.congr_hom
    (singularHomology₀Section_naturality (ModuleCat.of R R) (cellAttachingMap j) p) 1
  simp only [ConcreteCategory.comp_apply] at hmap
  have hval : (TopPair.ofSubset ({x}ᶜ : Set (skeletonObj C 1))).singularHomologyπ
      (ModuleCat.of R R) 0 (SSet.homologyMap (TopCat.toSSet.map (cellAttachingMap j))
        (ModuleCat.of R R) 0 ((reducedSingularHomologyι (ModuleCat.of R R) 0).app
          (TopCat.diskBoundary.{w} 1)
            ((reducedSingularHomologyTopCatSphereIso (ModuleCat.of R R) 0).inv 1))) =
      (if ((cellAttachingMap j sphereMinus : skeletonObj C 1) : X) ∈ openCell 0 i then
        cellLocalClass C (ModuleCat.of R R) x hx 1 else 0) -
      if ((cellAttachingMap j spherePlus : skeletonObj C 1) : X) ∈ openCell 0 i then
        cellLocalClass C (ModuleCat.of R R) x hx 1 else 0 := by
    rw [hgen]
    -- The singular homology of the boundary sphere and of the skeleton appear both through
    -- `singularHomologyFunctor` and through `SSet.homology`, which agree only up to unfolding.
    erw [map_sub, map_sub, hmap, hmap]
    rw [singularHomologyπ_singularHomology₀Section_apply_one C R x hx,
      singularHomologyπ_singularHomology₀Section_apply_one C R x hx]
  have hL : inv (cellLocalClass C (ModuleCat.of R R) x hx)
      (cellLocalClass C (ModuleCat.of R R) x hx 1) = 1 := by
    rw [← ModuleCat.comp_apply, IsIso.hom_inv_id, ModuleCat.id_apply]
  rw [cellularIncidence_eq_inv_cellLocalClass C R x hx j]
  -- `hval` is stated with the boundary sphere `TopCat.diskBoundary 1`, which the goal presents
  -- as `TopCat.diskBoundary (0 + 1)`.
  erw [hval]
  split_ifs <;> simp [hL]

/-- **Injective attaching maps of `1`-cells have unit incidence numbers.** If the attaching map
of a `1`-cell `j` is injective, then every `0`-cell in the frontier of `j` has incidence number
`1` or `-1` in the cellular boundary of `j`; in particular it is a unit. -/
theorem isUnit_cellularIncidence_zero_of_injective {i : cell C 0} {j : cell C 1}
    (hinj : Function.Injective (cellAttachingMap j))
    (hi : openCell 0 i ⊆ cellFrontier 1 j) :
    IsUnit (cellularIncidence C R 0 i j) := by
  classical
  obtain ⟨x₀, hx₀⟩ := openCell_nonempty 0 i
  rw [← range_cellAttachingMap] at hi
  obtain ⟨q, hq⟩ := hi hx₀
  have hpt (p : TopCat.diskBoundary.{w} 1) :
      ((cellAttachingMap j p : skeletonObj C 1) : X) ∈ openCell 0 i ↔ p = q := by
    rw [openCell_zero_eq_singleton, Set.mem_singleton_iff]
    have hx₀' := hx₀
    rw [openCell_zero_eq_singleton, Set.mem_singleton_iff] at hx₀'
    rw [← hx₀', ← hq]
    exact ⟨fun h ↦ hinj (Subtype.ext h), fun h ↦ h ▸ rfl⟩
  rw [cellularIncidence_zero]
  simp only [hpt]
  rcases eq_sphereMinus_or_eq_spherePlus q with rfl | rfl
  · simp [sphereMinus_ne_spherePlus.symm]
  · simp [sphereMinus_ne_spherePlus]

end TauCeti
