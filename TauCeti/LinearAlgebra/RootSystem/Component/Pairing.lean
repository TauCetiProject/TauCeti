/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.IsValuedIn
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import TauCeti.LinearAlgebra.RootSystem.Component.Basic

/-!
# The root pairing of an irreducible component

The roots and coroots of an irreducible component of a finite root system over a field form a root
pairing on the component space and its coroot analogue, whose non-orthogonality graph is the
component. It is a root system, irreducible when `2 ≠ 0` in the field, so each component gives an
irreducible root system and, by `RootPairing.isInternal_componentSpace`, the ambient space is the
direct sum of their spaces. The component pairing inherits being crystallographic and being
reduced.

The pairing between the two component spaces is perfect because a root or coroot of a component is
orthogonal to everything in the other components, so nondegeneracy of the ambient pairing already
holds on the component.

## Main definitions

* `RootPairing.componentPairing`: the root pairing of an irreducible component.

## Main results

* `RootPairing.nonorthogonalGraph_componentPairing`: the graph of the component pairing is the
  component.
* `RootPairing.isIrreducible_componentPairing`: the component pairing is irreducible when
  `2 ≠ 0` in the field.
* `RootPairing.componentProj_reflection_of_eq`: the projection onto the component space of `C`
  carries the reflections at roots of `C` to the reflections of the component pairing.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2.
* J. S. Milne, *Algebraic Groups*, Cambridge University Press (2017), Appendix C, C.23 and C.55.
-/

public section

open Submodule (span)

namespace RootPairing

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N)

variable {P} in
/-- The ambient pairing restricted to a component space and its coroot analogue is perfect. -/
instance isPerfPair_domRestrict₁₂_componentSpace [Finite ι] [P.IsRootSystem] (C : P.Component) :
    (P.toLinearMap.domRestrict₁₂ (P.componentSpace C) (P.corootComponentSpace C)).IsPerfPair := by
  have : FiniteDimensional K (P.componentSpace C) := by
    rw [componentSpace_def]
    exact FiniteDimensional.span_of_finite K (Set.toFinite _)
  refine .of_injective ?_ ?_
  · refine injective_iff_map_eq_zero _ |>.mpr fun x hx ↦ Subtype.ext ?_
    refine P.eq_zero_iff_forall_coroot'_eq_zero.mpr fun j ↦ ?_
    by_cases hj : P.componentOf j = C
    · simpa [LinearMap.domRestrict₁₂_apply] using
        LinearMap.congr_fun hx ⟨P.coroot j, hj ▸ coroot_mem_corootComponentSpace j⟩
    · exact coroot'_eq_zero_of_mem_componentSpace hj x.2
  · refine injective_iff_map_eq_zero _ |>.mpr fun y hy ↦ Subtype.ext ?_
    refine P.flip.eq_zero_iff_forall_coroot'_eq_zero.mpr fun j ↦ ?_
    by_cases hj : P.componentOf j = C
    · simpa [LinearMap.domRestrict₁₂_apply] using
        LinearMap.congr_fun hy ⟨P.root j, hj ▸ root_mem_componentSpace j⟩
    · exact root'_eq_zero_of_mem_corootComponentSpace hj y.2

/-- The **root pairing of an irreducible component** of a finite root system over a field: the roots
and coroots of the component, on the component space and its coroot analogue. The reflection
permutations are those of the ambient pairing, by `RootPairing.componentOf_reflectionPerm`. -/
noncomputable def componentPairing [Finite ι] [P.IsRootSystem] (C : P.Component) :
    RootPairing C.supp K (P.componentSpace C) (P.corootComponentSpace C) where
  toLinearMap := P.toLinearMap.domRestrict₁₂ _ _
  root := ⟨fun i ↦ ⟨P.root i, root_mem_componentSpace_of_mem_supp i.2⟩,
    fun _ _ h ↦ Subtype.ext (P.root.injective (congrArg Subtype.val h))⟩
  coroot := ⟨fun i ↦ ⟨P.coroot i, coroot_mem_corootComponentSpace_of_mem_supp i.2⟩,
    fun _ _ h ↦ Subtype.ext (P.coroot.injective (congrArg Subtype.val h))⟩
  root_coroot_two i := P.root_coroot_two i
  reflectionPerm i := (P.reflectionPerm i).subtypeEquiv fun j ↦ by
    simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, componentOf_reflectionPerm]
  reflectionPerm_root i j := Subtype.ext (P.reflectionPerm_root i j)
  reflectionPerm_coroot i j := Subtype.ext (P.reflectionPerm_coroot i j)

section

variable [Finite ι] [P.IsRootSystem] (C : P.Component)

@[simp]
theorem coe_componentPairing_root (i : C.supp) :
    ((P.componentPairing C).root i : M) = P.root i :=
  (rfl)

@[simp]
theorem coe_componentPairing_coroot (i : C.supp) :
    ((P.componentPairing C).coroot i : N) = P.coroot i :=
  (rfl)

@[simp]
theorem componentPairing_toLinearMap_apply (x : P.componentSpace C)
    (y : P.corootComponentSpace C) :
    (P.componentPairing C).toLinearMap x y = P.toLinearMap x y :=
  (rfl)

@[simp]
theorem componentPairing_pairing (i j : C.supp) :
    (P.componentPairing C).pairing i j = P.pairing i j :=
  (rfl)

@[simp]
theorem coe_componentPairing_reflectionPerm (i j : C.supp) :
    ((P.componentPairing C).reflectionPerm i j : ι) = P.reflectionPerm i j :=
  (rfl)

@[simp]
theorem coe_componentPairing_reflection_apply (i : C.supp) (x : P.componentSpace C) :
    ((P.componentPairing C).reflection i x : M) = P.reflection i x :=
  (rfl)

variable {P C} in
/-- The component projection carries the reflection at a root of `C` to the reflection of the
component pairing. -/
theorem componentProj_reflection_of_eq {i : ι} (h : P.componentOf i = C) (x : M) :
    P.componentProj C (P.reflection i x) =
      (P.componentPairing C).reflection ⟨i, h⟩ (P.componentProj C x) := by
  ext
  rw [coe_componentProj_reflection, coe_componentPairing_reflection_apply]

/-- The non-orthogonality graph of the component pairing is the component itself, as an induced
subgraph of the ambient non-orthogonality graph. -/
theorem nonorthogonalGraph_componentPairing :
    (P.componentPairing C).nonorthogonalGraph = C.toSimpleGraph := by
  ext i j
  simp [SimpleGraph.ConnectedComponent.toSimpleGraph, IsOrthogonal, Subtype.ext_iff]

instance isRootSystem_componentPairing : (P.componentPairing C).IsRootSystem where
  span_root_eq_top :=
    (Submodule.span_range_subtype_eq_top_iff _ fun i : C.supp ↦
      root_mem_componentSpace_of_mem_supp i.2).mpr <| by
        rw [componentSpace_def, Set.image_eq_range]
  span_coroot_eq_top :=
    (Submodule.span_range_subtype_eq_top_iff _ fun i : C.supp ↦
      coroot_mem_corootComponentSpace_of_mem_supp i.2).mpr <| by
        rw [corootComponentSpace_def, Set.image_eq_range]

/-- **The root pairing of an irreducible component is irreducible.** -/
instance isIrreducible_componentPairing [NeZero (2 : K)] : (P.componentPairing C).IsIrreducible :=
  isIrreducible_iff_connected_nonorthogonalGraph.mpr <| by
    rw [nonorthogonalGraph_componentPairing]
    exact C.connected_toSimpleGraph

instance isCrystallographic_componentPairing [P.IsCrystallographic] :
    (P.componentPairing C).IsCrystallographic where
  exists_value i j := IsValuedIn.exists_value (P := P) (S := ℤ) (i : ι) j

instance isReduced_componentPairing [P.IsReduced] : (P.componentPairing C).IsReduced where
  eq_or_eq_neg i j hij := by
    have hinj : ¬ LinearIndependent K ![P.root i, P.root j] := fun h ↦ hij <| by
      refine LinearIndependent.of_comp (P.componentSpace C).subtype ?_
      convert h using 1
      ext k
      fin_cases k <;> rfl
    refine (IsReduced.eq_or_eq_neg (P := P) i j hinj).imp (fun h ↦ ?_) fun h ↦ ?_
    · exact Subtype.ext h
    · exact Subtype.ext h

end

end RootPairing
