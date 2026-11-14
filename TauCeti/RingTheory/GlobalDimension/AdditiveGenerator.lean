/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.Algebra
public import TauCeti.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.CategoryTheory.Functor.RingEquivEnd
public import TauCeti.CategoryTheory.Preadditive.AdditiveGenerator
public import TauCeti.CategoryTheory.Preadditive.Projectivization
public import TauCeti.RingTheory.GlobalDimension.MulOpposite

/-!
# Global dimension of the endomorphism ring of an additive generator

Let `C` be a preadditive category with finite biproducts and kernels, `M` an additive generator of
`C` and `Γ = End M`. Then every finitely presented right `Γ`-module has projective dimension at most
two, so the right global dimension of `Γ` is at most two when `Γ` is right Noetherian, and so is its
left global dimension when `Γ` is also left Noetherian.

For an additive generator `M` of `mod A = FGModuleCat A`, where `A` is a finite algebra over a
commutative Noetherian ring, for instance an Artin algebra, this gives
`TauCeti.globalDimension (Module.End A M) ≤ 2`: the global dimension half of the statement that
`Module.End A M` is an Auslander algebra.

## Main results

* `TauCeti.IsAdditiveGenerator.hasProjectiveDimensionLE_two`: every finitely presented right
  `End M`-module has projective dimension at most two.
* `TauCeti.IsAdditiveGenerator.globalDimension_mulOpposite_end_le_two`: the right global dimension
  of a right Noetherian `End M` is at most two.
* `TauCeti.IsAdditiveGenerator.globalDimension_end_le_two`: the left global dimension of a left and
  right Noetherian `End M` is at most two.
* `TauCeti.IsAdditiveGenerator.globalDimension_moduleEnd_le_two`: for an additive generator `M` of
  `mod A` over a finite algebra `A` over a commutative Noetherian ring,
  `TauCeti.globalDimension (Module.End A M) ≤ 2`.

## Implementation notes

A finitely presented right `Γ`-module `N` is the cokernel of a map between free modules of finite
rank. By projectivization (`TauCeti.preadditiveCoyonedaObjBiproductIso`,
`TauCeti.preadditiveCoyonedaObj_map_bijective`) this map is `Hom(M, φ)` for some `φ : Mᵐ ⟶ Mⁿ`, and
`0 ⟶ Hom(M, ker φ) ⟶ Hom(M, Mᵐ) ⟶ Hom(M, Mⁿ) ⟶ N ⟶ 0` is a projective resolution, as in
`TauCeti.hasProjectiveDimensionLE_two_of_hasKernels` for `mod C`. We work with modules directly
rather than transporting projective dimension from `mod C`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Proposition VI.5.4(a).
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

namespace IsAdditiveGenerator

section Category

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C] [HasKernels C]
  {M : C}

/-- If `M` is an additive generator of a preadditive category with kernels, every finitely
presented right `End M`-module has projective dimension at most two. -/
theorem hasProjectiveDimensionLE_two (hM : IsAdditiveGenerator M) (N : ModuleCat.{v} (End M)ᵐᵒᵖ)
    [Module.FinitePresentation (End M)ᵐᵒᵖ N] : HasProjectiveDimensionLE N 2 := by
  obtain ⟨n, m, g, f, hg, hfg⟩ := Module.FinitePresentation.exists_fin' (End M)ᵐᵒᵖ N
  let S : ShortComplex (ModuleCat.{v} (End M)ᵐᵒᵖ) :=
    .mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) (ModuleCat.hom_ext hfg.linearMap_comp_eq_zero)
  have : Epi S.g := (ModuleCat.epi_iff_surjective _).2 hg
  have hS : S.Exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hfg
  -- The free modules are `Hom(M, Mᵐ)` and `Hom(M, Mⁿ)`, and `f` is composition with some `φ`.
  let eX := preadditiveCoyonedaObjBiproductIso M m
  let eY := preadditiveCoyonedaObjBiproductIso M n
  obtain ⟨φ, hφ⟩ := (preadditiveCoyonedaObj_map_bijective (additiveClosure_biproduct m) _).2
    (eX.hom ≫ S.f ≫ eY.inv)
  -- Its kernel is `Hom(M, ker φ)`, which is projective since `ker φ` lies in `add M`.
  have hK : Projective (kernel S.f) := by
    have := (finiteProjectiveModules_iff.1
      (finiteProjectiveModules_preadditiveCoyonedaObj_obj (hM.additiveClosure (kernel φ)))).2
    exact Projective.of_iso ((PreservesKernel.iso (preadditiveCoyonedaObj M) φ).trans
      (kernel.mapIso _ _ eX eY (by simp only [hφ, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]))) inferInstance
  have := (hasProjectiveDimensionLT_cokernel_iff_kernel S.f 0).2
    (projective_iff_hasProjectiveDimensionLT_one.1 hK)
  exact hasProjectiveDimensionLT_of_iso (X := cokernel S.f)
    ((cokernelIsCokernel S.f).coconePointUniqueUpToIso hS.gIsCokernel) 3

/-- If `M` is an additive generator of a preadditive category with kernels and `End M` is right
Noetherian, then the right global dimension of `End M` is at most two. -/
theorem globalDimension_mulOpposite_end_le_two (hM : IsAdditiveGenerator M)
    [IsNoetherianRing (End M)ᵐᵒᵖ] : globalDimension.{v} (End M)ᵐᵒᵖ ≤ 2 := by
  refine ((globalDimension_le_tfae.{v} (End M)ᵐᵒᵖ 2).out 1 2).2 fun N hN ↦ ?_
  have := Module.finitePresentation_of_finite (End M)ᵐᵒᵖ N (h := hN)
  exact hM.hasProjectiveDimensionLE_two N

/-- If `M` is an additive generator of a preadditive category with kernels and `End M` is left and
right Noetherian, then the left global dimension of `End M` is at most two. -/
theorem globalDimension_end_le_two (hM : IsAdditiveGenerator M) [IsNoetherianRing (End M)]
    [IsNoetherianRing (End M)ᵐᵒᵖ] : globalDimension.{v} (End M) ≤ 2 :=
  (globalDimension_le_globalDimension_mulOpposite (End M)).trans
    hM.globalDimension_mulOpposite_end_le_two

end Category

open scoped ModuleCat.Algebra in
/-- **The global dimension of an Auslander algebra.** If `M` is an additive generator of
`mod A = FGModuleCat A`, for a finite algebra `A` over a commutative Noetherian ring, for instance
an Artin algebra, then `Module.End A M` has global dimension at most two. -/
theorem globalDimension_moduleEnd_le_two {R : Type*} [CommRing R] [IsNoetherianRing R]
    {A : Type u} [Ring A] [Algebra R A] [Module.Finite R A] {M : FGModuleCat.{v} A}
    (hM : IsAdditiveGenerator M) : globalDimension.{v} (Module.End A M.obj) ≤ 2 := by
  have : IsNoetherianRing A := isNoetherian_of_tower R inferInstance
  have : Module.Finite R (End M) := Module.Finite.equiv End.linearEquiv.symm
  have : Module.Finite R (End M)ᵐᵒᵖ := Module.Finite.equiv (MulOpposite.opLinearEquiv R)
  have : IsNoetherianRing (End M) := isNoetherian_of_tower R inferInstance
  have : IsNoetherianRing (End M)ᵐᵒᵖ := isNoetherian_of_tower R inferInstance
  let e : End M ≃+* Module.End A M.obj :=
    ((ObjectProperty.fullyFaithfulι (ModuleCat.isFG A)).ringEquivEnd M).trans
      (ModuleCat.endRingEquiv M.obj)
  rw [← e.globalDimension_eq]
  exact hM.globalDimension_end_le_two

end IsAdditiveGenerator

end TauCeti
