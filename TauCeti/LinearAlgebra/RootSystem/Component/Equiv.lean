/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.InvariantForm

/-!
# Invariant forms of the components under equivalences of root pairings

An equivalence of root pairings `e : P ≃ Q` carries the irreducible components of `P` to those of
`Q` (`RootPairing.Equiv.componentEquiv`) and the component spaces to the component spaces
(`RootPairing.Equiv.map_componentSpace`). This file upgrades that to an equivalence of the
component pairings, `RootPairing.Equiv.componentPairingEquiv e C`, from the root pairing of the
component `C` to that of the corresponding component of `Q`.

The description of the invariant forms of a root system by its components is then natural in the
root pairing: restricting the pullback of an invariant form to a component is pulling back its
restriction to the corresponding component along the equivalence of component pairings, and the
orthogonal reconstruction commutes with the pullbacks in the same way. The naturality of the
component scales themselves is `RootPairing.InvariantForm.componentScale_comap`.

## Main definitions

* `RootPairing.Equiv.componentPairingEquiv`: the equivalence of component pairings induced by an
  equivalence of root pairings.

## Main results

* `RootPairing.InvariantForm.restrictComponent_comap`: restriction to a component commutes with the
  pullbacks.
* `RootPairing.InvariantForm.comap_ofComponent`: orthogonal reconstruction commutes with the
  pullbacks.

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
theorem coe_componentPairingEquiv_indexEquiv_apply (e : P.Equiv Q) (C : P.Component)
    (i : C.supp) : ((e.componentPairingEquiv C).indexEquiv i : ι₂) = e.indexEquiv i :=
  (rfl)

end Equiv

/-! ### Restriction and reconstruction under the pullback -/

namespace InvariantForm

/-- **Restricting the pullback of an invariant form to a component** is pulling back its
restriction to the corresponding component along the equivalence of component pairings. -/
theorem restrictComponent_comap (e : P.Equiv Q) (B : Q.InvariantForm) (C : P.Component) :
    (comap e.toHom B).restrictComponent C =
      comap (e.componentPairingEquiv C).toHom (B.restrictComponent (e.componentEquiv C)) := by
  ext x y
  simp

/-- **Orthogonal reconstruction commutes with the pullbacks**: the pullback of the orthogonal sum
of a family of component forms is the orthogonal sum of their pullbacks along the equivalences of
component pairings, reindexed along the bijection of components. -/
theorem comap_ofComponent [NeZero (2 : K)] (e : P.Equiv Q)
    (G : ∀ D, (Q.componentPairing D).InvariantForm) :
    comap e.toHom (ofComponent G) =
      ofComponent fun C ↦ comap (e.componentPairingEquiv C).toHom (G (e.componentEquiv C)) := by
  refine componentEquiv.injective (funext fun C ↦ ?_)
  rw [componentEquiv_apply, componentEquiv_apply, restrictComponent_comap,
    restrictComponent_ofComponent, restrictComponent_ofComponent]

end InvariantForm

end RootPairing
