/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.Pairing
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Weyl groups of irreducible components

For a finite root system `P` over a field, the Weyl group decomposes as the direct product of the
Weyl groups of the irreducible component pairings `P.componentPairing C`:

`P.weylGroup ≃* ∀ C : P.Component, (P.componentPairing C).weylGroup`.

Each reflection preserves every irreducible component and acts as the corresponding component
reflection on its own component space while fixing the other component spaces pointwise. Every
Weyl-group element therefore restricts to a Weyl-group element on each component, and since
reflections in distinct components act on complementary subspaces, the combined restriction map is
an isomorphism of groups.

## Main definitions

* `RootPairing.weylGroupComponentProj`: restriction of the Weyl group to the Weyl group of an
  irreducible component.
* `RootPairing.weylGroupComponentEquiv`: the group isomorphism from `P.weylGroup` to the product of
  the Weyl groups `(P.componentPairing C).weylGroup` over `C : P.Component`.
* `RootPairing.weylGroupComponentLift`: inclusion of a component Weyl group into `P.weylGroup`,
  acting trivially on the other components.

## Main results

* `RootPairing.componentProj_weylGroup_smul`: the component projection `P.componentProj C`
  intertwines the action of `w : P.weylGroup` with `P.weylGroupComponentProj C w`.
* `RootPairing.natCard_weylGroup_eq_prod_componentPairing`: the order of `P.weylGroup` is the
  product of the orders of the component Weyl groups.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §1, no. 2, Proposition 5.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990), §2.2.
-/

public section

namespace RootPairing

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-- Every element of the Weyl group fixes each irreducible component of the non-orthogonality
graph. -/
theorem componentEquiv_eq_of_mem_weylGroup {g : P.Aut} (hg : g ∈ P.weylGroup) (C : P.Component) :
    g.componentEquiv C = C := by
  induction C using SimpleGraph.ConnectedComponent.ind with | _ j => ?_
  refine (Equiv.componentEquiv_componentOf _ _).trans ?_
  induction hg using weylGroup.induction generalizing j with
  | mem i => exact componentOf_reflectionPerm i j
  | one => rfl
  | mul _ y _ _ hx hy => exact (hx (y.indexEquiv j)).trans (hy j)

/-- Every component space is invariant under the weight-space representation of the Weyl group. -/
theorem componentSpace_mem_invtSubmodule_weylGroupRootRep (C : P.Component) (w : P.weylGroup) :
    P.componentSpace C ∈ Module.End.invtSubmodule (P.weylGroupRootRep w) := fun _ hx ↦ by
  have hmap := w.1.map_componentSpace C
  rw [P.componentEquiv_eq_of_mem_weylGroup w.2 C] at hmap
  exact hmap ▸ Submodule.mem_map_of_mem hx

private theorem mem_componentSpace_weylGroup_smul (C : P.Component) (w : P.weylGroup) {x : M}
    (hx : x ∈ P.componentSpace C) : w.1.toHom.weightMap x ∈ P.componentSpace C :=
  P.componentSpace_mem_invtSubmodule_weylGroupRootRep C w hx

end CommRing

section Field

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem]

/-- Restriction of a Weyl-group element to an endomorphism of the component root pairing. -/
private noncomputable def weylGroupComponentEnd (C : P.Component) (w : P.weylGroup) :
    End (P.componentPairing C) where
  weightMap := w.1.toHom.weightMap.restrict fun _ hx ↦
    P.mem_componentSpace_weylGroup_smul C w hx
  coweightMap := w.1.toHom.coweightMap.restrict fun _ hy ↦ by
    have hmap := w.1.map_corootComponentSpace C
    rw [P.componentEquiv_eq_of_mem_weylGroup w.2 C] at hmap
    exact hmap ▸ Submodule.mem_map_of_mem hy
  indexEquiv := w.1.indexEquiv.subtypeEquiv fun i ↦ by
    simpa [P.componentEquiv_eq_of_mem_weylGroup w.2 C] using
      (w.1.indexEquiv_mem_supp_iff (C := C) (i := i)).symm
  weight_coweight_transpose := by
    ext ⟨y, _⟩ ⟨x, _⟩
    simpa [LinearMap.coe_restrict_apply] using
      congr($(Hom.weight_coweight_transpose_apply P P y w.1.toHom) x)
  root_weightMap := funext fun _ ↦ Subtype.ext <| by
    rw [Function.comp_apply, LinearMap.coe_restrict_apply, coe_componentPairing_root,
      Hom.root_weightMap_apply]; simp
  coroot_coweightMap := funext fun _ ↦ Subtype.ext <| by
    rw [Function.comp_apply, LinearMap.coe_restrict_apply, coe_componentPairing_coroot,
      Hom.coroot_coweightMap_apply]; simp

/-- Restriction of a Weyl-group element to an automorphism of the component root pairing. -/
private noncomputable def weylGroupComponentAutHom (C : P.Component) :
    P.weylGroup →* Aut (P.componentPairing C) where
  toFun w :=
    have hmul : (w.1 * (w⁻¹).1).toHom = 1 := by rw [Subgroup.coe_inv, mul_inv_cancel]; rfl
    have hmul' : ((w⁻¹).1 * w.1).toHom = 1 := by rw [Subgroup.coe_inv, inv_mul_cancel]; rfl
    { toHom := P.weylGroupComponentEnd C w
      bijective_weightMap := _root_.Equiv.bijective
        ⟨(P.weylGroupComponentEnd C w).weightMap, (P.weylGroupComponentEnd C w⁻¹).weightMap,
          fun x ↦ Subtype.ext (congrArg (fun h : End P ↦ h.weightMap x.1) hmul'),
          fun x ↦ Subtype.ext (congrArg (fun h : End P ↦ h.weightMap x.1) hmul)⟩
      bijective_coweightMap := _root_.Equiv.bijective
        ⟨(P.weylGroupComponentEnd C w).coweightMap, (P.weylGroupComponentEnd C w⁻¹).coweightMap,
          fun y ↦ Subtype.ext (congrArg (fun h : End P ↦ h.coweightMap y.1) hmul),
          fun y ↦ Subtype.ext (congrArg (fun h : End P ↦ h.coweightMap y.1) hmul')⟩ }
  map_one' := by apply Equiv.indexHom_injective; ext; rfl
  map_mul' _ _ := by apply Equiv.indexHom_injective; ext; rfl

private theorem weylGroupComponentAutHom_ofIdx_of_eq {C : P.Component} {i : ι}
    (hi : P.componentOf i = C) :
    P.weylGroupComponentAutHom C (weylGroup.ofIdx P i) =
      Equiv.reflection (P.componentPairing C) ⟨i, hi⟩ := by
  apply Equiv.indexHom_injective; ext j
  exact (coe_componentPairing_reflectionPerm P C ⟨i, hi⟩ j).symm

private theorem weylGroupComponentAutHom_ofIdx_of_ne {C : P.Component} {i : ι}
    (hi : P.componentOf i ≠ C) :
    P.weylGroupComponentAutHom C (weylGroup.ofIdx P i) = 1 := by
  apply Equiv.indexHom_injective; ext ⟨j, hj⟩
  exact P.reflectionPerm_eq_of_pairing_eq_zero
    (isOrthogonal_of_componentOf_ne (hi.trans_eq hj.symm)).2

private theorem weylGroupComponentAutHom_mem (C : P.Component) (w : P.weylGroup) :
    P.weylGroupComponentAutHom C w ∈ (P.componentPairing C).weylGroup := by
  obtain ⟨g, hg⟩ := w
  induction hg using weylGroup.induction with
  | mem i =>
    change P.weylGroupComponentAutHom C (weylGroup.ofIdx P i) ∈ _
    by_cases hi : P.componentOf i = C
    · exact P.weylGroupComponentAutHom_ofIdx_of_eq hi ▸
        (P.componentPairing C).reflection_mem_weylGroup ⟨i, hi⟩
    · exact P.weylGroupComponentAutHom_ofIdx_of_ne hi ▸ one_mem _
  | one => exact (P.weylGroupComponentAutHom C).map_one ▸ one_mem _
  | mul _ _ hx hy ihx ihy =>
    rw [← Submonoid.mk_mul_mk _ _ _ hx hy, map_mul]
    exact mul_mem ihx ihy

/-- **Restriction of the Weyl group to an irreducible component.** Every element of `P.weylGroup`
restricts on `P.componentSpace C` to an element of `(P.componentPairing C).weylGroup`. -/
noncomputable def weylGroupComponentProj (C : P.Component) :
    P.weylGroup →* (P.componentPairing C).weylGroup :=
  (P.weylGroupComponentAutHom C).codRestrict _ (P.weylGroupComponentAutHom_mem C)

/-- On `P.componentSpace C`, `P.weylGroupComponentProj C w` acts by the ambient Weyl action of
`w`. -/
@[simp]
theorem coe_weylGroupComponentProj_smul (C : P.Component) (w : P.weylGroup)
    (x : P.componentSpace C) :
    ((P.weylGroupComponentProj C w • x : P.componentSpace C) : M) = w • (x : M) :=
  (rfl)

/-- A reflection in `C` restricts on `C` to the corresponding component reflection. -/
theorem weylGroupComponentProj_ofIdx_of_eq {C : P.Component} {i : ι} (hi : P.componentOf i = C) :
    P.weylGroupComponentProj C (weylGroup.ofIdx P i) =
      weylGroup.ofIdx (P.componentPairing C) ⟨i, hi⟩ :=
  Subtype.ext (P.weylGroupComponentAutHom_ofIdx_of_eq hi)

/-- A reflection outside `C` acts trivially on `C`. -/
theorem weylGroupComponentProj_ofIdx_of_ne {C : P.Component} {i : ι} (hi : P.componentOf i ≠ C) :
    P.weylGroupComponentProj C (weylGroup.ofIdx P i) = 1 :=
  Subtype.ext (P.weylGroupComponentAutHom_ofIdx_of_ne hi)

/-- **The component projection intertwines the Weyl-group action** on `M` with the action of the
component Weyl group on `P.componentSpace C`. -/
@[simp]
theorem componentProj_weylGroup_smul (C : P.Component) (w : P.weylGroup) (x : M) :
    P.componentProj C (w • x) = P.weylGroupComponentProj C w • P.componentProj C x := by
  let _ : Fintype P.Component := Fintype.ofFinite P.Component
  conv_lhs => rw [← P.sum_componentProj x]
  rw [Finset.smul_sum, map_sum, Finset.sum_eq_single C]
  · have hmem : w • (P.componentProj C x : M) ∈ P.componentSpace C :=
      P.componentSpace_mem_invtSubmodule_weylGroupRootRep C w (P.componentProj C x).2
    rw [componentProj_apply_of_mem hmem]; rfl
  · intro D _ hDC
    have hmem : w • (P.componentProj D x : M) ∈ P.componentSpace D :=
      P.componentSpace_mem_invtSubmodule_weylGroupRootRep D w (P.componentProj D x).2
    exact componentProj_apply_of_ne hDC hmem
  · exact fun hC ↦ absurd (Finset.mem_univ C) hC

private theorem mulSingle_mem_range_pi_weylGroupComponentProj [DecidableEq P.Component]
    (C : P.Component) (u : (P.componentPairing C).weylGroup) :
    Pi.mulSingle C u ∈ (MonoidHom.pi P.weylGroupComponentProj).range := by
  obtain ⟨g, hg⟩ := u
  induction hg using weylGroup.induction with
  | mem i =>
    refine ⟨weylGroup.ofIdx P i.1, funext fun D ↦ ?_⟩
    by_cases hDC : D = C
    · subst hDC; rw [MonoidHom.pi_apply, Pi.mulSingle_eq_same]
      exact P.weylGroupComponentProj_ofIdx_of_eq i.2
    · rw [MonoidHom.pi_apply, Pi.mulSingle_eq_of_ne hDC]
      exact P.weylGroupComponentProj_ofIdx_of_ne (i.2.trans_ne (Ne.symm hDC))
  | one => exact ⟨1, by rw [map_one]; exact (Pi.mulSingle_one C).symm⟩
  | mul _ _ hx hy ihx ihy =>
    rw [← Submonoid.mk_mul_mk _ _ _ hx hy, Pi.mulSingle_mul]
    exact mul_mem ihx ihy

/-- **The Weyl group of a finite root system is the direct product of the Weyl groups of its
irreducible components.** -/
noncomputable def weylGroupComponentEquiv :
    P.weylGroup ≃* ∀ C : P.Component, (P.componentPairing C).weylGroup :=
  MulEquiv.ofBijective (MonoidHom.pi P.weylGroupComponentProj)
    ⟨fun u v huv ↦ weylGroup.ext fun x ↦ by
      let _ : Fintype P.Component := Fintype.ofFinite P.Component
      rw [← P.sum_componentProj (u • x), ← P.sum_componentProj (v • x)]
      refine Finset.sum_congr rfl fun C _ ↦ congrArg Subtype.val ?_
      rw [componentProj_weylGroup_smul, componentProj_weylGroup_smul,
        show P.weylGroupComponentProj C u = P.weylGroupComponentProj C v from congrFun huv C],
     fun f ↦ by
      classical
      let _ : Fintype P.Component := Fintype.ofFinite P.Component
      let φ := MonoidHom.pi P.weylGroupComponentProj
      suffices ∀ s : Finset P.Component, (fun D ↦ if D ∈ s then f D else 1) ∈ φ.range by
        simpa using this Finset.univ
      intro s; induction s using Finset.induction_on with
      | empty =>
        exact (show (fun D : P.Component ↦ if D ∈ (∅ : Finset P.Component) then f D else 1) = 1 from
          funext fun _ ↦ by simp) ▸ one_mem φ.range
      | insert C s hC ih =>
        have heq : (fun D ↦ if D ∈ insert C s then f D else 1) =
            Pi.mulSingle C (f C) * (fun D ↦ if D ∈ s then f D else 1) := funext fun D ↦ by
          by_cases hDC : D = C
          · subst hDC; simp [hC]
          · simp [hDC]
        exact heq ▸ mul_mem (P.mulSingle_mem_range_pi_weylGroupComponentProj C (f C)) ih⟩

/-- At component `C`, `P.weylGroupComponentEquiv w` is `P.weylGroupComponentProj C w`. -/
@[simp]
theorem weylGroupComponentEquiv_apply (w : P.weylGroup) (C : P.Component) :
    P.weylGroupComponentEquiv w C = P.weylGroupComponentProj C w :=
  (rfl)

/-- **Inclusion of an irreducible component's Weyl group into `P.weylGroup`**, acting as the
identity on all other component spaces. -/
noncomputable def weylGroupComponentLift [DecidableEq P.Component] (C : P.Component) :
    (P.componentPairing C).weylGroup →* P.weylGroup :=
  P.weylGroupComponentEquiv.symm.toMonoidHom.comp
    (MonoidHom.mulSingle (fun D ↦ (P.componentPairing D).weylGroup) C)

/-- `weylGroupComponentProj C` is a left inverse to `weylGroupComponentLift C`. -/
@[simp]
theorem weylGroupComponentProj_weylGroupComponentLift_self [DecidableEq P.Component]
    (C : P.Component) (u : (P.componentPairing C).weylGroup) :
    P.weylGroupComponentProj C (P.weylGroupComponentLift C u) = u := by
  simpa [weylGroupComponentLift] using
    congrFun (P.weylGroupComponentEquiv.apply_symm_apply (Pi.mulSingle C u)) C

/-- `weylGroupComponentLift C u` projects to `1` on every component `D ≠ C`. -/
theorem weylGroupComponentProj_weylGroupComponentLift_of_ne [DecidableEq P.Component]
    {C D : P.Component} (hDC : D ≠ C) (u : (P.componentPairing C).weylGroup) :
    P.weylGroupComponentProj D (P.weylGroupComponentLift C u) = 1 := by
  simpa [weylGroupComponentLift, Pi.mulSingle_eq_of_ne hDC] using
    congrFun (P.weylGroupComponentEquiv.apply_symm_apply (Pi.mulSingle C u)) D

/-- Lifting a component reflection into `P.weylGroup` gives the ambient reflection at the same
root index. -/
@[simp]
theorem weylGroupComponentLift_ofIdx [DecidableEq P.Component] (C : P.Component) (i : C.supp) :
    P.weylGroupComponentLift C (weylGroup.ofIdx (P.componentPairing C) i) =
      weylGroup.ofIdx P i.1 := by
  apply P.weylGroupComponentEquiv.injective
  funext D
  by_cases hDC : D = C
  · subst hDC
    simp [P.weylGroupComponentProj_ofIdx_of_eq i.2]
  · rw [weylGroupComponentEquiv_apply, weylGroupComponentProj_weylGroupComponentLift_of_ne P hDC,
      weylGroupComponentEquiv_apply,
      P.weylGroupComponentProj_ofIdx_of_ne (i.2.trans_ne (Ne.symm hDC))]

/-- **The order of the Weyl group is the product of the orders of the component Weyl groups.** -/
theorem natCard_weylGroup_eq_prod_componentPairing [Fintype P.Component] :
    Nat.card P.weylGroup = ∏ C : P.Component, Nat.card (P.componentPairing C).weylGroup := by
  rw [Nat.card_congr P.weylGroupComponentEquiv.toEquiv, Nat.card_pi]

end Field

end RootPairing
