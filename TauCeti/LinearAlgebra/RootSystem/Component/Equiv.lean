/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.InvariantForm
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Equiv

/-!
# Invariant forms of the components under equivalences of root pairings

An equivalence of root pairings `e : P ≃ Q` carries the irreducible components of `P` to those of
`Q` (`RootPairing.Equiv.componentEquiv`) and the component spaces to the component spaces
(`RootPairing.Equiv.map_componentSpace`). This file upgrades that to an equivalence of the
component pairings, `RootPairing.Equiv.componentPairingEquiv e C`, from the root pairing of the
component `C` to that of the corresponding component of `Q`.

The description of the invariant forms of a root system by its components is then natural in the
root pairing. Restricting the pushforward of an invariant form to a component is pushing forward
its restriction along the equivalence of component pairings, and the orthogonal reconstruction
commutes with the pushforwards in the same way. The scale of an invariant form against a
reference form on a component is unchanged when both forms are pushed forward, so the bijection
between positive-definite invariant forms and positive scales, one per component, only reindexes
the scales along the bijection of components. Since the canonical root form is carried to the
canonical root form, the scales measured against the canonical forms are intrinsic: an automorphism
of a root system permuting its components permutes the scales of an invariant form in the same way.

## Main definitions

* `RootPairing.Equiv.componentPairingEquiv`: the equivalence of component pairings induced by an
  equivalence of root pairings.

## Main results

* `RootPairing.InvariantForm.restrictComponent_map`: restriction to a component commutes with the
  pushforwards.
* `RootPairing.InvariantForm.map_ofComponent`: orthogonal reconstruction commutes with the
  pushforwards.
* `RootPairing.InvariantForm.componentScale_map`: the scale on a component is unchanged when both
  forms are pushed forward.
* `RootPairing.InvariantForm.componentScale_toInvariantForm_map`: measured against the canonical
  forms, the scales are carried along the bijection of components.
* `RootPairing.InvariantForm.posDefEquivScale_map`: the parametrization of positive-definite
  invariant forms by positive scales reindexes the scales along the bijection of components.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2.
* J. S. Milne, *Algebraic Groups*, Cambridge University Press (2017), Appendix C, C(g) and C.55.
-/

public section

namespace RootPairing

variable {ι K M N ι₂ M₂ N₂ : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup M₂] [Module K M₂] [AddCommGroup N₂] [Module K N₂]
  {P : RootPairing ι K M N} {Q : RootPairing ι₂ K M₂ N₂}
  [Finite ι] [P.IsRootSystem] [Finite ι₂] [Q.IsRootSystem]

/-! ### The equivalence of component pairings -/

namespace Equiv

/-- The **equivalence of component pairings** induced by an equivalence of root pairings `e`: the
restrictions of the weight and coweight equivalences of `e` to the component spaces of `C` and of
the corresponding component of `Q`, along the bijection of the roots of the two components. -/
noncomputable def componentPairingEquiv (e : P.Equiv Q) (C : P.Component) :
    (P.componentPairing C).Equiv (Q.componentPairing (e.componentEquiv C)) where
  weightMap := (e.weightEquiv.submoduleMap (P.componentSpace C)).trans
    (LinearEquiv.ofEq _ _ (e.map_componentSpace C))
  coweightMap := ((e.coweightEquiv.submoduleMap
    (Q.corootComponentSpace (e.componentEquiv C))).trans
      (LinearEquiv.ofEq _ _ (e.map_corootComponentSpace C))).toLinearMap
  indexEquiv := e.indexEquiv.subtypeEquiv fun _ ↦ e.indexEquiv_mem_supp_iff.symm
  weight_coweight_transpose := by
    ext y x
    simpa using e.toLinearMap_weightEquiv x.1 y.1
  root_weightMap := by
    ext i
    simp [Hom.root_weightMap_apply]
  coroot_coweightMap := by
    ext i
    simp [Hom.coroot_coweightMap_apply]
  bijective_weightMap := LinearEquiv.bijective _
  bijective_coweightMap := LinearEquiv.bijective _

@[simp]
theorem coe_componentPairingEquiv_weightMap_apply (e : P.Equiv Q) (C : P.Component)
    (x : P.componentSpace C) :
    ((e.componentPairingEquiv C).toHom.weightMap x : M₂) = e.toHom.weightMap x :=
  (rfl)

@[simp]
theorem coe_componentPairingEquiv_weightEquiv_symm_apply (e : P.Equiv Q) (C : P.Component)
    (x : Q.componentSpace (e.componentEquiv C)) :
    ((e.componentPairingEquiv C).weightEquiv.symm x : M) = e.weightEquiv.symm x := by
  rw [← e.weightEquiv.injective.eq_iff, LinearEquiv.apply_symm_apply, weightEquiv_apply,
    ← coe_componentPairingEquiv_weightMap_apply, ← weightEquiv_apply, LinearEquiv.apply_symm_apply]

@[simp]
theorem coe_componentPairingEquiv_indexEquiv_apply (e : P.Equiv Q) (C : P.Component)
    (i : C.supp) : ((e.componentPairingEquiv C).indexEquiv i : ι₂) = e.indexEquiv i :=
  (rfl)

end Equiv

/-! ### Restriction and reconstruction under the pushforward -/

namespace InvariantForm

/-- **Restricting the pushforward of an invariant form to a component** is pushing forward its
restriction along the equivalence of component pairings. -/
theorem restrictComponent_map (e : P.Equiv Q) (B : P.InvariantForm) (C : P.Component) :
    (B.map e).restrictComponent (e.componentEquiv C) =
      (B.restrictComponent C).map (e.componentPairingEquiv C) := by
  ext x y
  simp

/-- **Orthogonal reconstruction commutes with the pushforwards**: the pushforward of the orthogonal
sum of a family of component forms is the orthogonal sum of their pushforwards along the
equivalences of component pairings, reindexed along the bijection of components. -/
theorem map_ofComponent [NeZero (2 : K)] (e : P.Equiv Q)
    (F : ∀ C, (P.componentPairing C).InvariantForm) (G : ∀ D, (Q.componentPairing D).InvariantForm)
    (hG : ∀ C, G (e.componentEquiv C) = (F C).map (e.componentPairingEquiv C)) :
    (ofComponent F).map e = ofComponent G := by
  refine componentEquiv.injective (funext fun D ↦ ?_)
  obtain ⟨C, rfl⟩ := e.componentEquiv.surjective D
  rw [componentEquiv_apply, componentEquiv_apply, restrictComponent_map,
    restrictComponent_ofComponent, restrictComponent_ofComponent, hG]

/-! ### Scales under the pushforward -/

variable [NeZero (2 : K)]

/-- **The scale of an invariant form on a component is unchanged when it and the reference form are
pushed forward** along an equivalence of root pairings, the component `C` going to the
corresponding component of `Q`. -/
@[simp]
theorem componentScale_map (e : P.Equiv Q) (B₀ B : P.InvariantForm) (C : P.Component) :
    componentScale (B₀.map e) (B.map e) (e.componentEquiv C) = componentScale B₀ B C := by
  obtain ⟨i, rfl⟩ : ∃ i, P.componentOf i = C := C.exists_rep
  rw [Equiv.componentEquiv_componentOf, componentScale_eq_div, componentScale_eq_div]
  simp

/-- **Measured against the canonical forms, the scales of an invariant form are carried along the
bijection of components.** In particular an automorphism of a root system permutes the scales of an
invariant form as it permutes the components. -/
theorem componentScale_toInvariantForm_map [Fintype ι] [Fintype ι₂] [P.IsAnisotropic]
    [Q.IsAnisotropic] (e : P.Equiv Q) (B : P.InvariantForm) (C : P.Component) :
    componentScale Q.toInvariantForm (B.map e) (e.componentEquiv C) =
      componentScale P.toInvariantForm B C := by
  rw [← map_toInvariantForm e, componentScale_map]

/-- **The parametrization of positive-definite invariant forms by positive scales is natural**: the
scales of the pushforward of a positive-definite form, against the pushforward of the reference
form, are its own scales reindexed along the bijection of components. -/
theorem posDefEquivScale_map [LinearOrder K] [IsStrictOrderedRing K] (e : P.Equiv Q)
    (B₀ : P.InvariantForm) (hB₀ : B₀.form.toQuadraticMap.PosDef)
    (B : {B : P.InvariantForm // B.form.toQuadraticMap.PosDef}) :
    posDefEquivScale (B₀.map e) (posDef_map_iff.mpr hB₀) ⟨B.1.map e, posDef_map_iff.mpr B.2⟩ =
      fun D ↦ posDefEquivScale B₀ hB₀ B (e.componentEquiv.symm D) := by
  ext D
  obtain ⟨C, rfl⟩ := e.componentEquiv.surjective D
  simp

end InvariantForm

end RootPairing
