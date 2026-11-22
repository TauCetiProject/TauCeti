/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import TauCeti.RepresentationTheory.Rep.OfMulDistribMulAction

/-!
# Functorial isomorphism on group cohomology of multiplicative group actions

Given action-intertwining group equivalences `eM : M' ≃* M` and `eG : G ≃* G'` between abelian
groups `M` and `M'` with `MulDistribMulAction`s of `G` and `G'`, Mathlib's
`groupCohomology.mapIso` applied to `Rep.ofMulDistribMulActionLinearEquiv` produces an isomorphism
`TauCeti.groupCohomology.relabelCohomologyIso : Hⁿ(G, M) ≅ Hⁿ(G', M')`.

Its forward and inverse morphisms are given in terms of `groupCohomology.map` by
`TauCeti.groupCohomology.relabelCohomologyIso_hom` and
`TauCeti.groupCohomology.relabelCohomologyIso_inv`.

## Main definitions

* `TauCeti.groupCohomology.relabelCohomologyIso`: the isomorphism `Hⁿ(G, M) ≅ Hⁿ(G', M')`
  induced by action-intertwining equivalences `eM : M' ≃* M` and `eG : G ≃* G'`.

## Main results

* `TauCeti.groupCohomology.relabelCohomologyIso_hom`,
  `TauCeti.groupCohomology.relabelCohomologyIso_inv`: the forward and inverse maps of
  `relabelCohomologyIso` in terms of `groupCohomology.map`.
-/

public section

namespace TauCeti.groupCohomology

open CategoryTheory _root_.groupCohomology

variable {G M G' M' : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
  [Group G'] [CommGroup M'] [MulDistribMulAction G' M']

/-- **Isomorphism on group cohomology induced by relabelling coefficients and acting group.**
Equivalences `eM : M' ≃* M` and `eG : G ≃* G'` intertwining the actions induce an isomorphism
`Hⁿ(G, M) ≅ Hⁿ(G', M')` in every degree `n`. -/
noncomputable def relabelCohomologyIso (eM : M' ≃* M) (eG : G ≃* G')
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m) (n : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction G M) n ≅
      groupCohomology (Rep.ofMulDistribMulAction G' M') n :=
  groupCohomology.mapIso eG (Rep.ofMulDistribMulActionLinearEquiv G G' eM)
    (Rep.ofMulDistribMulActionLinearEquiv_isIntertwining eM eG hsmul) n

/-- The forward map of `relabelCohomologyIso` is `groupCohomology.map` along `eG.symm` and
`Rep.ofMulDistribMulActionResHom`. -/
theorem relabelCohomologyIso_hom (eM : M' ≃* M) (eG : G ≃* G')
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m) (n : ℕ) :
    (relabelCohomologyIso eM eG hsmul n).hom =
      groupCohomology.map eG.symm.toMonoidHom
        (Rep.ofMulDistribMulActionResHom eM eG hsmul) n := by
  rw [relabelCohomologyIso, groupCohomology.mapIso_hom]
  refine congrArg (fun φ ↦ groupCohomology.map eG.symm.toMonoidHom φ n)
    (Rep.hom_ext <| Representation.IntertwiningMap.ext ?_)
  exact (Rep.ofMulDistribMulActionResHom_hom_toLinearMap eM eG hsmul).symm

/-- The inverse map of `relabelCohomologyIso` is `groupCohomology.map` along `eG` and
`Rep.ofMulDistribMulActionResHom` for the inverse equivalences. -/
theorem relabelCohomologyIso_inv (eM : M' ≃* M) (eG : G ≃* G')
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m) (n : ℕ) :
    (relabelCohomologyIso eM eG hsmul n).inv =
      groupCohomology.map eG.toMonoidHom
        (Rep.ofMulDistribMulActionResHom eM.symm eG.symm fun g' m ↦ by
          simpa using (eM.symm_apply_eq.2
            ((hsmul (eG.symm g') (eM.symm m)).trans (by simp))).symm) n := by
  rw [relabelCohomologyIso, groupCohomology.mapIso_inv]
  refine congrArg (fun φ ↦ groupCohomology.map eG.toMonoidHom φ n)
    (Rep.hom_ext <| Representation.IntertwiningMap.ext ?_)
  exact (congrArg LinearEquiv.toLinearMap (Rep.ofMulDistribMulActionLinearEquiv_symm eM)).trans
    (Rep.ofMulDistribMulActionResHom_hom_toLinearMap eM.symm eG.symm _).symm

end TauCeti.groupCohomology
