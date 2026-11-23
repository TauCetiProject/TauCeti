/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Fibration
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.HomotopyInvariance
public import TauCeti.Topology.Category.TopCat.Pullback
public import TauCeti.Topology.PathSpace.Moore.Replacement.Equiv

/-!
# The DG local system of a map of fibrations

A commutative square of continuous maps
```
E --h--> E'
|p       |p'
B --g--> B'
```
with `g b = b'` induces the map `(e, γ) ↦ (h e, g ∘ γ)` from the fibre `F'_p` over `b` of the
Moore-path replacement of `p` to the fibre `F'_{p'}` over `b'`
(`TauCeti.MooreReplacement.Fiber.squareMap`). It intertwines the actions of the Moore loops
through `Ω g : Ω_b B → Ω_{b'} B'`, so on chains it is a morphism
`C_*(F'_p) → g^* C_*(F'_{p'})` of DG local systems on `(B, b)`, from the DG local system of `p` to
the pullback of the DG local system of `p'` (restriction of scalars along `C_*(Ω g)`). Over the
identity of `B` it is the naturality morphism `TauCeti.fibrationLocalSystemMap` of maps over `B`.

When `p` and `p'` are Hurewicz fibrations and `h` restricts to a homotopy equivalence from the
fibre of `p` over `b` to the fibre of `p'` over `b'`, this morphism is a quasi-isomorphism: the
fibres of both replacements are homotopy equivalent to the fibres of `p` and `p'`, compatibly
with the map. In particular, for the base change `B ×_{B'} E' → B` of a Hurewicz fibration `p'`
along any map `g`, the DG local system of the base change is quasi-isomorphic to the pullback
along `g` of the DG local system of `p'`: pulling back fibrations and pulling back their DG local
systems agree up to quasi-isomorphism, so the coefficients of a pulled-back fibration in DG Morse
homology are computed from those of the original fibration.

## Main definitions

* `TauCeti.fibrationLocalSystemSquareMap R h g hsq hg`: the morphism
  `C_*(F'_p) → g^* C_*(F'_{p'})` induced by a commutative square.

## Main results

* `TauCeti.fibrationLocalSystemSquareMap_id`, `TauCeti.fibrationLocalSystemSquareMap_comp`:
  over the identity of the base it is `TauCeti.fibrationLocalSystemMap`, and pasting squares
  composes the induced morphisms.
* `TauCeti.isQuasiIso_fibrationLocalSystemSquareMap`: for Hurewicz fibrations, it is a
  quasi-isomorphism when `h` is a homotopy equivalence on the fibres.
* `TauCeti.isQuasiIso_fibrationLocalSystemSquareMap_pullbackSnd`: the DG local system of the base
  change of a Hurewicz fibration is quasi-isomorphic to the pullback of its DG local system.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 7.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
-/

public section

noncomputable section

open CategoryTheory MulOpposite ContinuousMap

namespace TauCeti

universe u

section SquareMap

variable {E E' B B' : Type u} [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  [TopologicalSpace B'] (R : Type*) [CommRing R] {p : C(E, B)} {p' : C(E', B')} {b : B} {b' : B'}

/-- The **morphism of DG local systems induced by a commutative square** `p' ∘ h = g ∘ p` with
`g b = b'`: the push-forward of chains along the map `(e, γ) ↦ (h e, g ∘ γ)` of the fibres of the
Moore-path replacements, from the DG local system of `p` at `b` to the pullback along `g` of the
DG local system of `p'` at `b'`. -/
def fibrationLocalSystemSquareMap (h : C(E, E')) (g : C(B, B')) (hsq : p'.comp h = g.comp p)
    (hg : g b = b') :
    fibrationLocalSystem R p b ⟶
      (DGLocalSystem.pullback R g hg).obj (fibrationLocalSystem R p' b') :=
  DGRightModuleCat.restrictScalarsHomMk _
    (cubicalChainModuleLinearMap R (MooreReplacement.Fiber.squareMap h g hsq hg))
    (fun a x ↦ by
      rw [cubicalChainModuleLinearMap_op_smul_map _ (MooreLoopSpace.map g hg).toContinuousMap
        (fun ω y ↦ MooreReplacement.Fiber.squareMap_act h g hsq hg y ω), loopChainMap_apply])
    (fun _ _ hx ↦ cubicalChainModuleLinearMap_mem _ hx)
    (fun x ↦ (cubicalChainModuleDifferential_linearMap _ x).symm)

/-- The morphism induced by a commutative square is the push-forward of chains along the map of
fibres. -/
@[simp]
theorem restrictScalarsEquiv_fibrationLocalSystemSquareMap_apply (h : C(E, E')) (g : C(B, B'))
    (hsq : p'.comp h = g.comp p) (hg : g b = b') (x : fibrationLocalSystem R p b) :
    DGRightModuleCat.restrictScalarsEquiv _ _ (fibrationLocalSystemSquareMap R h g hsq hg x) =
      cubicalChainModuleLinearMap (G' := MooreLoopSpace B' b') R
        (MooreReplacement.Fiber.squareMap h g hsq hg) x := by
  rw [fibrationLocalSystemSquareMap,
    DGRightModuleCat.restrictScalarsEquiv_restrictScalarsHomMk_apply]

/-- **Over the identity of the base**, the morphism induced by a commutative square is the
morphism `TauCeti.fibrationLocalSystemMap` of a map over `B`, read through the identification of
the pullback along the identity. -/
theorem fibrationLocalSystemSquareMap_id {q : C(E', B)} (h : C(E, E')) (hh : q.comp h = p) :
    fibrationLocalSystemSquareMap R (b := b) h (.id B) (by rw [ContinuousMap.id_comp, hh])
        (ContinuousMap.id_apply b) ≫
      (DGLocalSystem.pullbackId R).hom.app (fibrationLocalSystem R q b) =
      fibrationLocalSystemMap R h hh := by
  ext x
  -- `simp` does not close this goal, nor the one in `fibrationLocalSystemSquareMap_comp`: it
  -- leaves `DGRightModuleCat.comp_apply` unused, and even after rewriting with it, it does not
  -- fire `restrictScalarsEquiv_fibrationLocalSystemSquareMap_apply` on the carrier of the
  -- pullback, so the chain of rewrites is spelled out.
  rw [DGRightModuleCat.comp_apply, DGLocalSystem.pullbackId_hom_app, DGRightModuleCat.comp_apply,
    DGRightModuleCat.restrictScalarsIdApp_hom_apply,
    DGRightModuleCat.restrictScalarsEquiv_eqToHom_apply (loopChainMap_id R),
    restrictScalarsEquiv_fibrationLocalSystemSquareMap_apply, fibrationLocalSystemMap_apply,
    MooreReplacement.Fiber.squareMap_id h hh]

/-- **Pasting two commutative squares** induces the composite of the induced morphisms, read
through the identification of the pullback along a composite with the composite of the pullbacks.
-/
theorem fibrationLocalSystemSquareMap_comp {E'' B'' : Type u} [TopologicalSpace E'']
    [TopologicalSpace B''] {p'' : C(E'', B'')} {b'' : B''} (h : C(E, E')) (g : C(B, B'))
    (h' : C(E', E'')) (g' : C(B', B'')) (hsq : p'.comp h = g.comp p)
    (hsq' : p''.comp h' = g'.comp p') (hg : g b = b') (hg' : g' b' = b'') :
    fibrationLocalSystemSquareMap R (h'.comp h) (g'.comp g)
        (by rw [← ContinuousMap.comp_assoc, hsq', ContinuousMap.comp_assoc, hsq,
          ContinuousMap.comp_assoc])
        (by rw [ContinuousMap.comp_apply, hg, hg']) ≫
      (DGLocalSystem.pullbackComp R g' g hg' hg).hom.app (fibrationLocalSystem R p'' b'') =
      fibrationLocalSystemSquareMap R h g hsq hg ≫
        (DGLocalSystem.pullback R g hg).map (fibrationLocalSystemSquareMap R h' g' hsq' hg') := by
  ext x
  apply (DGRightModuleCat.restrictScalarsEquiv (loopChainMap R g hg) _).injective
  apply (DGRightModuleCat.restrictScalarsEquiv (loopChainMap R g' hg') _).injective
  rw [DGRightModuleCat.comp_apply, DGLocalSystem.pullbackComp_hom_app, DGRightModuleCat.comp_apply,
    DGRightModuleCat.restrictScalarsCompApp_hom_apply,
    DGRightModuleCat.restrictScalarsEquiv_eqToHom_apply (loopChainMap_comp R g' g hg' hg),
    restrictScalarsEquiv_fibrationLocalSystemSquareMap_apply, DGRightModuleCat.comp_apply,
    DGRightModuleCat.restrictScalars_map_apply,
    restrictScalarsEquiv_fibrationLocalSystemSquareMap_apply,
    restrictScalarsEquiv_fibrationLocalSystemSquareMap_apply,
    MooreReplacement.Fiber.squareMap_comp h g h' g' hsq hsq' hg hg',
    cubicalChainModuleLinearMap_comp, LinearMap.comp_apply]

end SquareMap

section QuasiIso

variable {E E' B B' : Type u} [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  [TopologicalSpace B'] {R : Type u} [CommRing R] {p : C(E, B)} {p' : C(E', B')} {b : B}
  {b' : B'}

/-- **A map of Hurewicz fibrations that is a homotopy equivalence on the fibres induces a
quasi-isomorphism of DG local systems** `C_*(F'_p) → g^* C_*(F'_{p'})`. -/
theorem isQuasiIso_fibrationLocalSystemSquareMap (hp : IsHurewiczFibration.{u} p)
    (hp' : IsHurewiczFibration.{u} p') (h : C(E, E')) (g : C(B, B'))
    (hsq : p'.comp h = g.comp p) (hg : g b = b') (e : {x // p x = b} ≃ₕ {x // p' x = b'})
    (he : ∀ x, (e x : E') = h x) :
    DGRightModuleCat.IsQuasiIso (fibrationLocalSystemSquareMap R h g hsq hg) :=
  isQuasiIso_restrictScalars_of_apply_eq R _ _
    (MooreReplacement.Fiber.squareMapHomotopyEquiv hp hp' h g hsq hg e he) fun x ↦ by
      rw [MooreReplacement.Fiber.squareMapHomotopyEquiv_toFun]
      exact restrictScalarsEquiv_fibrationLocalSystemSquareMap_apply R h g hsq hg x

/-- **The DG local system of a base change is the pullback of the DG local system.** For a
Hurewicz fibration `p' : E' → B'` and any map `g : B → B'`, the morphism from the DG local system
at `b` of the base change `B ×_{B'} E' → B` to the pullback along `g` of the DG local system of
`p'` at `g b`, induced by the projection `B ×_{B'} E' → E'`, is a quasi-isomorphism. -/
theorem isQuasiIso_fibrationLocalSystemSquareMap_pullbackSnd (hp' : IsHurewiczFibration.{u} p')
    (g : C(B, B')) (b : B) :
    DGRightModuleCat.IsQuasiIso (fibrationLocalSystemSquareMap R
      (p := (TopCat.pullbackFst (TopCat.ofHom g) (TopCat.ofHom p')).hom) (p' := p') (b := b)
      (TopCat.pullbackSnd (TopCat.ofHom g) (TopCat.ofHom p')).hom g
      (ContinuousMap.ext fun x ↦ x.property.symm) rfl) :=
  isQuasiIso_fibrationLocalSystemSquareMap (hp'.pullback g) hp' _ g _ rfl
    (TopCat.homeoOfIso ((TopCat.ofHom p').fiberPullbackFstIso (TopCat.ofHom g) b)).toHomotopyEquiv
    fun x ↦ TopCat.Hom.fiberPullbackFstIso_hom_apply_coe (TopCat.ofHom p') (TopCat.ofHom g) b x

end QuasiIso

end TauCeti

end
