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
reduced. An equivalence of root pairings `e : P ≃ Q` restricts to an equivalence from the pairing
of each component `C` of `P` to that of the corresponding component `e.componentEquiv C` of `Q`.

The pairing between the two component spaces is perfect because a root or coroot of a component is
orthogonal to everything in the other components, so nondegeneracy of the ambient pairing already
holds on the component.

## Main definitions

* `RootPairing.componentPairing`: the root pairing of an irreducible component.
* `RootPairing.Equiv.componentPairingEquiv`: the equivalence of component pairings induced by an
  equivalence of root pairings.

## Main results

* `RootPairing.nonorthogonalGraph_componentPairing`: the graph of the component pairing is the
  component.
* `RootPairing.isIrreducible_componentPairing`: the component pairing is irreducible when
  `2 ≠ 0` in the field.
* `RootPairing.componentProj_reflection_of_eq`: the projection onto the component space of `C`
  carries the reflections at roots of `C` to the reflections of the component pairing.
* `RootPairing.Equiv.componentPairingEquiv_weightMap_componentProj`: the equivalence of component
  pairings intertwines the projections onto the component spaces.

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
    · exact coroot'_eq_zero_of_mem_componentSpace hj x.property
  · refine injective_iff_map_eq_zero _ |>.mpr fun y hy ↦ Subtype.ext ?_
    refine P.flip.eq_zero_iff_forall_coroot'_eq_zero.mpr fun j ↦ ?_
    by_cases hj : P.componentOf j = C
    · simpa [LinearMap.domRestrict₁₂_apply] using
        LinearMap.congr_fun hy ⟨P.root j, hj ▸ root_mem_componentSpace j⟩
    · exact root'_eq_zero_of_mem_corootComponentSpace hj y.property

/-- The **root pairing of an irreducible component** of a finite root system over a field: the roots
and coroots of the component, on the component space and its coroot analogue. The reflection
permutations are those of the ambient pairing, by `RootPairing.componentOf_reflectionPerm`. -/
noncomputable def componentPairing [Finite ι] [P.IsRootSystem] (C : P.Component) :
    RootPairing C.supp K (P.componentSpace C) (P.corootComponentSpace C) where
  toLinearMap := P.toLinearMap.domRestrict₁₂ _ _
  root := ⟨fun i ↦ ⟨P.root i, root_mem_componentSpace_of_mem_supp i.property⟩,
    fun _ _ h ↦ Subtype.ext (P.root.injective (congrArg Subtype.val h))⟩
  coroot := ⟨fun i ↦ ⟨P.coroot i, coroot_mem_corootComponentSpace_of_mem_supp i.property⟩,
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
      root_mem_componentSpace_of_mem_supp i.property).mpr <| by
        rw [componentSpace_def, Set.image_eq_range]
  span_coroot_eq_top :=
    (Submodule.span_range_subtype_eq_top_iff _ fun i : C.supp ↦
      coroot_mem_corootComponentSpace_of_mem_supp i.property).mpr <| by
        rw [corootComponentSpace_def, Set.image_eq_range]

/-- **The root pairing of an irreducible component is irreducible.** -/
instance isIrreducible_componentPairing [NeZero (2 : K)] : (P.componentPairing C).IsIrreducible :=
  isIrreducible_iff_connected_nonorthogonalGraph.mpr <| by
    rw [nonorthogonalGraph_componentPairing]
    exact C.connected_toSimpleGraph

instance isValuedIn_componentPairing (S : Type*) [CommRing S] [Algebra S K] [P.IsValuedIn S] :
    (P.componentPairing C).IsValuedIn S where
  exists_value i j := IsValuedIn.exists_value (P := P) (S := S) (i : ι) j

/-- The `S`-valued pairings of the component pairing are those of the ambient pairing. -/
@[simp]
theorem componentPairing_pairingIn (S : Type*) [CommRing S] [Algebra S K] [P.IsValuedIn S]
    (i j : C.supp) : (P.componentPairing C).pairingIn S i j = P.pairingIn S i j :=
  (rfl)

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

/-! ### The equivalence of component pairings -/

namespace Equiv

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module K M₂] [AddCommGroup N₂] [Module K N₂]
  {P} {Q : RootPairing ι₂ K M₂ N₂} [Finite ι] [P.IsRootSystem] [Finite ι₂] [Q.IsRootSystem]

/-- The **equivalence of component pairings** induced by an equivalence of root pairings `e`: the
restrictions of the weight and coweight equivalences of `e` to the component spaces of `C` and of
the corresponding component `D = e.componentEquiv C` of `Q`, along the bijection of the roots of the
two components. Taking `D` with a proof `hD` of this equality, rather than `e.componentEquiv C`
itself, lets an automorphism mapping `C` to itself restrict to an automorphism of the pairing
of `C`. -/
noncomputable def componentPairingEquiv (e : P.Equiv Q) (C : P.Component) {D : Q.Component}
    (hD : e.componentEquiv C = D) : (P.componentPairing C).Equiv (Q.componentPairing D) where
  weightMap := (e.weightEquiv.submoduleMap (P.componentSpace C)).trans
    (LinearEquiv.ofEq _ _ ((e.map_componentSpace C).trans (congrArg Q.componentSpace hD)))
  coweightMap := ((e.coweightEquiv.submoduleMap (Q.corootComponentSpace D)).trans
    (LinearEquiv.ofEq _ _ ((congrArg (fun D ↦ (Q.corootComponentSpace D).map
      e.coweightEquiv.toLinearMap) hD.symm).trans (e.map_corootComponentSpace C)))).toLinearMap
  indexEquiv := e.indexEquiv.subtypeEquiv fun _ ↦ hD ▸ e.indexEquiv_mem_supp_iff.symm
  weight_coweight_transpose := by
    ext y x
    simpa using e.toLinearMap_weightEquiv x.val y.val
  root_weightMap := by
    ext i
    simp [Hom.root_weightMap_apply]
  coroot_coweightMap := by
    ext i
    simp [Hom.coroot_coweightMap_apply]
  bijective_weightMap := LinearEquiv.bijective _
  bijective_coweightMap := LinearEquiv.bijective _

section Apply

variable (e : P.Equiv Q) (C : P.Component) {D : Q.Component} (hD : e.componentEquiv C = D)

@[simp]
theorem coe_componentPairingEquiv_weightMap_apply (x : P.componentSpace C) :
    ((e.componentPairingEquiv C hD).toHom.weightMap x : M₂) = e.toHom.weightMap x :=
  (rfl)

@[simp]
theorem coe_componentPairingEquiv_coweightMap_apply (y : Q.corootComponentSpace D) :
    ((e.componentPairingEquiv C hD).toHom.coweightMap y : N) = e.toHom.coweightMap y :=
  (rfl)

@[simp]
theorem coe_componentPairingEquiv_indexEquiv_apply (i : C.supp) :
    ((e.componentPairingEquiv C hD).indexEquiv i : ι₂) = e.indexEquiv i :=
  (rfl)

/-- The inverse weight equivalence of component pairings acts as `e.weightEquiv.symm`. -/
@[simp]
theorem coe_componentPairingEquiv_weightEquiv_symm_apply (x : Q.componentSpace D) :
    ((e.componentPairingEquiv C hD).weightEquiv.symm x : M) = e.weightEquiv.symm x :=
  e.weightEquiv.injective <| by
    rw [e.weightEquiv_apply, ← coe_componentPairingEquiv_weightMap_apply e C hD,
      ← weightEquiv_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The inverse coweight equivalence of component pairings acts as `e.coweightEquiv.symm`. -/
@[simp]
theorem coe_componentPairingEquiv_coweightEquiv_symm_apply (y : P.corootComponentSpace C) :
    ((e.componentPairingEquiv C hD).coweightEquiv.symm y : N₂) = e.coweightEquiv.symm y :=
  e.coweightEquiv.injective <| by
    rw [e.coweightEquiv_apply, ← coe_componentPairingEquiv_coweightMap_apply e C hD,
      ← coweightEquiv_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The inverse index bijection of component pairings acts as `e.indexEquiv.symm`. -/
@[simp]
theorem coe_componentPairingEquiv_indexEquiv_symm_apply (j : D.supp) :
    ((e.componentPairingEquiv C hD).indexEquiv.symm j : ι) = e.indexEquiv.symm j :=
  (rfl)

/-- **The equivalence of component pairings intertwines the component projections**: projecting
onto the component space of `C` and then applying the equivalence of component pairings is
applying `e` and then projecting onto the component space of the corresponding component. -/
theorem componentPairingEquiv_weightMap_componentProj (x : M) :
    (e.componentPairingEquiv C hD).toHom.weightMap (P.componentProj C x) =
      Q.componentProj D (e.toHom.weightMap x) := by
  subst hD
  apply Subtype.ext
  rw [coe_componentPairingEquiv_weightMap_apply, ← e.coe_componentProj_weightMap C x]

end Apply

theorem componentPairingEquiv_congr {e₁ e₂ : P.Equiv Q} (he : e₁ = e₂) {C : P.Component}
    {D : Q.Component} (h₁ : e₁.componentEquiv C = D) (h₂ : e₂.componentEquiv C = D) :
    e₁.componentPairingEquiv C h₁ = e₂.componentPairingEquiv C h₂ := by
  subst he; rfl

/-- The identity equivalence restricts to the identity on every component. -/
@[simp]
theorem componentPairingEquiv_id (C : P.Component) :
    (Equiv.id P).componentPairingEquiv C (D := C) (by simp) = Equiv.id (P.componentPairing C) := by
  ext x <;> simp

/-- The identity automorphism restricts to the identity on every component. -/
@[simp]
theorem componentPairingEquiv_one (C : P.Component) :
    (1 : P.Aut).componentPairingEquiv C (D := C) (by simp) = 1 :=
  componentPairingEquiv_id C

/-- Restriction of component-fixing automorphisms to a component is multiplicative. -/
theorem componentPairingEquiv_mul {τ₁ τ₂ : P.Aut} {C : P.Component}
    (h₁ : τ₁.componentEquiv C = C) (h₂ : τ₂.componentEquiv C = C) :
    (τ₁ * τ₂).componentPairingEquiv C (by simp [h₁, h₂]) =
      τ₁.componentPairingEquiv C h₁ * τ₂.componentPairingEquiv C h₂ := by
  ext x <;> simp [Equiv.mul_eq_comp]

/-- Restriction of component-fixing automorphisms to a component preserves inverses. -/
@[simp]
theorem componentPairingEquiv_inv {τ : P.Aut} {C : P.Component}
    (hC : τ.componentEquiv C = C) :
    (τ⁻¹).componentPairingEquiv C
        (by rw [componentEquiv_inv, _root_.Equiv.Perm.inv_eq_iff_eq, hC]) =
      (τ.componentPairingEquiv C hC)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by
    rw [← componentPairingEquiv_mul, componentPairingEquiv_congr (inv_mul_cancel τ) _ (by simp),
      componentPairingEquiv_one]

/-- Restriction of component-fixing automorphisms to a component preserves natural powers. -/
@[simp]
theorem componentPairingEquiv_pow {τ : P.Aut} {C : P.Component}
    (hC : τ.componentEquiv C = C) (n : ℕ) :
    (τ ^ n).componentPairingEquiv C
        (by rw [componentEquiv_pow]; exact Function.IsFixedPt.perm_pow hC n) =
      τ.componentPairingEquiv C hC ^ n := by
  induction n with
  | zero => exact componentPairingEquiv_one C
  | succ n ih =>
    have hpow : (τ ^ n).componentEquiv C = C := by
      rw [componentEquiv_pow]; exact Function.IsFixedPt.perm_pow hC n
    simp only [pow_succ', componentPairingEquiv_mul hC hpow, ih]

/-- **Conjugating `τ.componentPairingEquiv C hC` along `e.componentPairingEquiv C hD` restricts
`e.autCongr τ` to `D`.** -/
theorem autCongr_componentPairingEquiv (e : P.Equiv Q) {τ : P.Aut} {C : P.Component}
    (hC : τ.componentEquiv C = C) {D : Q.Component} (hD : e.componentEquiv C = D) :
    (e.componentPairingEquiv C hD).autCongr (τ.componentPairingEquiv C hC) =
      (e.autCongr τ).componentPairingEquiv D
        (by subst hD; simp [autCongr_apply, hC]) := by
  ext x <;> simp [autCongr_apply]

end Equiv

end RootPairing
