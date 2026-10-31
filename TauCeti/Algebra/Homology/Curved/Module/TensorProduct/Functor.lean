/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.TensorProduct.Basic
public import TauCeti.Algebra.Homology.Curved.Module.Right.Homotopy
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Tensoring curved right modules with a curved left module

Fix a curved left module `N` over a curved DG algebra `(A, d, w)`, so `dN (dN n) = -(w • n)`.
For every curved right module `M` the balanced tensor product `M ⊗_A N` is an ordinary cochain
complex, because the two curvature actions cancel
(`TauCeti.BalancedTensorProduct.curvedCochainComplex`). This file makes that construction a
functor of `M`.

* On the closed degree-zero category of curved right modules, a closed morphism `f` acts by
  `f ⊗ 1`, giving a functor to cochain complexes of ground-ring modules.
* An odd homotopy `k` between closed morphisms gives the homotopy `k ⊗ 1` between the induced
  chain maps. Hence the functor descends to a functor from the curved homotopy category to
  Mathlib's homotopy category of cochain complexes.

Curved modules have no cohomology, so the second functor is the meaningful one: it is the
underived tensor product `- ⊗_A N` on curved homotopy categories, with no flatness hypothesis.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.tensorCochainComplexFunctor`: tensoring with `N` on the closed
  degree-zero category of curved right modules.
* `TauCeti.CurvedDGRightModuleCat.tensorHomotopyFunctor`: its descent to the curved homotopy
  category, valued in `HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)`.

## Main results

* `TauCeti.CurvedDGRightModuleCat.homotopic_tensorCochainComplexFunctor_map`: closed morphisms
  with the same class in the curved homotopy category have homotopic images.
* `TauCeti.CurvedDGRightModuleCat.dgClosedToHomotopyCompTensorHomotopyFunctorIso`: the
  descended functor restricts along the quotient functor to tensoring followed by Mathlib's
  quotient functor.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and
  comodule-contramodule correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, for
  the tensor product of a right and a left CDG-module and its compatibility with homotopies.
  His curvature is the negative of the right-module curvature used here.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- The closed category keeps the original enriched object carrier.
attribute [local implicit_reducible] ForgetEnrichment

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}
  {N : Type u} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  {𝒩 : ℤ → Submodule R N} [DirectSum.Decomposition 𝒩] [SetLike.GradedSMul 𝒜 𝒩]
  {dN : N →ₗ[R] N} (hN : IsCurvedDGLeftModule h 𝒩 dN)

/-- The balanced tensor complex of a closed morphism `f` and the identity of `N`. -/
noncomputable abbrev tensorCochainComplexMap {M M' : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M') :
    BalancedTensorProduct.curvedCochainComplex M.isCurvedDGRightModule hN ⟶
      BalancedTensorProduct.curvedCochainComplex M'.isCurvedDGRightModule hN :=
  BalancedTensorProduct.curvedCochainComplexMap M.isCurvedDGRightModule hN
    M'.isCurvedDGRightModule hN ((closedHom f).restrictScalars R) LinearMap.id
    (fun a m ↦ (closedHom f).map_smul (op a) m) (fun _ _ ↦ rfl) (isHomogeneous_closedHom f)
    (LinearMap.isHomogeneous_id 𝒩) (differential_comp_closedHom f) rfl

/-- Tensoring closed curved right modules with the curved left module `N`: a curved right module
`M` goes to the balanced tensor complex `M ⊗_A N`, and a closed morphism `f` to `f ⊗ 1`. -/
@[expose]
noncomputable def tensorCochainComplexFunctor :
    ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) ⥤
      CochainComplex (ModuleCat.{u} R) ℤ where
  obj M := BalancedTensorProduct.curvedCochainComplex
    (ForgetEnrichment.to (CochainComplex (ModuleCat R) ℤ) M).isCurvedDGRightModule hN
  map f := tensorCochainComplexMap hN f
  map_id M := by
    refine (BalancedTensorProduct.curvedCochainComplexMap_congr _ _ _ _ _ _ _ _ _ _ _ _
      (LinearMap.ext fun x ↦ ?_) rfl).trans
        (BalancedTensorProduct.curvedCochainComplexMap_id _ _)
    exact LinearMap.congr_fun (closedHom_id (ForgetEnrichment.to _ M)) x
  map_comp {X Y Z} f g := by
    refine (BalancedTensorProduct.curvedCochainComplexMap_congr _ _ _ _ _ _ _ _ _ _ _ _
      (LinearMap.ext fun x ↦ ?_) rfl).trans
        (BalancedTensorProduct.curvedCochainComplexMap_comp _ hN _ hN _ LinearMap.id _
          (fun _ _ ↦ rfl) (isHomogeneous_closedHom f) (LinearMap.isHomogeneous_id 𝒩)
          (differential_comp_closedHom f) rfl
          (ForgetEnrichment.to (CochainComplex (ModuleCat R) ℤ) Z).isCurvedDGRightModule hN
          ((closedHom g).restrictScalars R) LinearMap.id _ (fun _ _ ↦ rfl)
          (isHomogeneous_closedHom g) (LinearMap.isHomogeneous_id 𝒩)
          (differential_comp_closedHom g) rfl)
    exact LinearMap.congr_fun (closedHom_comp f g) x

/-- The functor sends a curved right module to its balanced tensor complex with `N`. -/
@[simp]
theorem tensorCochainComplexFunctor_obj (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (tensorCochainComplexFunctor hN).obj (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) =
      BalancedTensorProduct.curvedCochainComplex M.isCurvedDGRightModule hN :=
  (rfl)

/-- The functor sends a closed morphism `f` to `f ⊗ 1`. -/
@[simp]
theorem tensorCochainComplexFunctor_map {M M' : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M') :
    (tensorCochainComplexFunctor hN).map f = tensorCochainComplexMap hN f :=
  (rfl)

/-- **Homotopy invariance.** Closed morphisms with the same class in the curved homotopy category
have homotopic images: an odd homotopy `k` from `f` to `g` gives the homotopy `k ⊗ 1`. -/
theorem homotopic_tensorCochainComplexFunctor_map {M M' : CurvedDGRightModuleCat.{u, u, u} h}
    (f g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M')
    (hfg : (dgClosedToHomotopy R).map f = (dgClosedToHomotopy R).map g) :
    Nonempty (Homotopy ((tensorCochainComplexFunctor hN).map f)
      ((tensorCochainComplexFunctor hN).map g)) := by
  obtain ⟨k, hk⟩ := (quotient_map_eq_iff_exists_homotopy f g).mp hfg
  exact ⟨BalancedTensorProduct.curvedCochainComplexMapHomotopy (k := k.1.restrictScalars R)
    (hk := fun a m ↦ k.1.map_smul (op a) m) (hk₁ := dgRightModuleCochains.mem_iff.mp k.2) _ _ _
    _ _ _ _ _ _ _ _ _ _ _ (LinearMap.ext fun x ↦ by
      simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        ForgetEnrichment.to_of]
        using sub_eq_iff_eq_add.mp (hk x))⟩

/-- Tensoring with the curved left module `N`, descended to the curved homotopy category. -/
@[expose]
noncomputable def tensorHomotopyFunctor :
    DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h) ⥤
      HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) :=
  DGHomotopyCategory.lift R
    (tensorCochainComplexFunctor hN ⋙ HomotopyCategory.quotient _ _) fun _ _ f g hfg ↦ by
      obtain ⟨H⟩ := homotopic_tensorCochainComplexFunctor_map hN f g hfg
      exact HomotopyCategory.eq_of_homotopy _ _ H

/-- The descended functor restricts along the quotient functor to tensoring with `N`
followed by Mathlib's quotient functor. -/
noncomputable def dgClosedToHomotopyCompTensorHomotopyFunctorIso :
    dgClosedToHomotopy R ⋙ tensorHomotopyFunctor hN ≅
      tensorCochainComplexFunctor hN ⋙ HomotopyCategory.quotient _ _ :=
  DGHomotopyCategory.dgClosedToHomotopyCompLiftIso R _ _

/-- The descended functor sends a curved right module to its balanced tensor complex. -/
@[simp]
theorem tensorHomotopyFunctor_obj_of (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (tensorHomotopyFunctor hN).obj (DGHomotopyCategory.of R M) =
      (HomotopyCategory.quotient _ _).obj
        (BalancedTensorProduct.curvedCochainComplex M.isCurvedDGRightModule hN) :=
  (rfl)

/-- The descended functor sends the class of a closed morphism `f` to the class of `f ⊗ 1`. -/
theorem tensorHomotopyFunctor_map_dgClosedToHomotopy_map
    {M M' : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M') :
    (tensorHomotopyFunctor hN).map ((dgClosedToHomotopy R).map f) =
      (HomotopyCategory.quotient _ _).map (tensorCochainComplexMap hN f) :=
  DGHomotopyCategory.lift_map_dgClosedToHomotopy_map R _ _ f

end TauCeti.CurvedDGRightModuleCat
