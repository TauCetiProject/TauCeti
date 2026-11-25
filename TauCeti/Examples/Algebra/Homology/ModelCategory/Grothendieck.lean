/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Sites.Sheafification
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExtensionByZero
public import TauCeti.Algebra.Homology.HomotopyCategory.KInjective
public import TauCeti.Algebra.Homology.ModelCategory.Grothendieck
public import TauCeti.Algebra.Module.ZMod.Injective
public import TauCeti.CategoryTheory.DG.CochainComplex.Fibrant
public import TauCeti.CategoryTheory.Linear.ULift
public import TauCeti.Examples.Algebra.Homology.UnboundedFlat

/-!
# Examples of the injective model structure on unbounded complexes

This file illustrates the injective model structure `CochainComplex.modelCategoryInjective` and
its fibrant DG enhancement `TauCeti.FibrantInjectiveDGCategory` in two directions:

1. **Sheaves of modules over an arbitrary sheaf of rings on a small site.** For any site `(C, J)`
   and any sheaf of (not necessarily commutative) rings `R : Sheaf J RingCat.{u}`,
   `SheafOfModules.{u} R` is Grothendieck abelian and `(ULift.{u} ℤ)`-linear via
   `CategoryTheory.Linear.ulift`. Consequently `CochainComplex (SheafOfModules.{u} R) ℤ` carries
   the injective model structure, the inclusion of `FibrantInjectiveDGCategory` into
   `KInjectiveDGCategory` is a quasi-equivalence of `(ULift.{u} ℤ)`-DG categories, and the homotopy
   category of `dgNerve (ULift.{u} ℤ) (FibrantInjectiveDGCategory (SheafOfModules.{u} R))` is
   equivalent to `DerivedCategory (SheafOfModules.{u} R)`. On a preorder site, restriction
   `SheafOfModules.overFunctor R U` to a lower interval preserves fibrations and fibrant complexes.

2. **Degreewise injectivity does not imply fibrancy for unbounded complexes.** Over the
   self-injective ring `ℤ/4`, every term of the unbounded acyclic two-periodic complex
   `⋯ → ℤ/4 --2--> ℤ/4 → ⋯` (`TauCeti.UnboundedFlat.complex`) is an injective object of
   `ModuleCat (ZMod 4)`, yet the complex is neither K-injective, nor fibrant in
   `CochainComplex.modelCategoryInjective`, nor an injective object of
   `CochainComplex (ModuleCat (ZMod 4)) ℤ`. Thus the K-injectivity condition in
   `CochainComplex.modelCategoryInjective.isFibrant_iff` is genuinely non-redundant on unbounded
   complexes, in contrast to bounded-below complexes (`CochainComplex.Plus.isFibrant_iff`).
-/

public section

noncomputable section

open CategoryTheory HomotopicalAlgebra Limits
open scoped CochainComplex.modelCategoryInjective

namespace TauCeti.Examples.ModelCategoryInjective

section SheafOfModules

universe u

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

-- Unbounded complexes of sheaves of modules over any sheaf of rings carry the injective model
-- structure and cardinal-controlled functorial fibrant replacement.
example : ModelCategory (CochainComplex (SheafOfModules.{u} R) ℤ) := inferInstance

example (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    IsFibrant ((CochainComplex.modelCategoryInjective.fibrantReplacement.{u}
      (SheafOfModules.{u} R)).obj K) :=
  inferInstance

/-- Over any sheaf of rings `R` on a small site, the `(ULift.{u} ℤ)`-DG inclusion of fibrant
injective complexes of `R`-modules into all K-injective complexes is a quasi-equivalence. -/
theorem isQuasiEquivalence_sheafOfModules :
    EnrichedFunctor.IsQuasiEquivalence
      (FibrantInjectiveDGCategory.toKInjectiveDGCategory (ULift.{u} ℤ) (SheafOfModules.{u} R)) :=
  FibrantInjectiveDGCategory.isQuasiEquivalence_toKInjectiveDGCategory.{u}
    (ULift.{u} ℤ) (SheafOfModules.{u} R)

/-- Over any sheaf of rings `R` on a small site, the differential graded nerve of fibrant injective
complexes of `R`-modules has homotopy category equivalent to `DerivedCategory (SheafOfModules R)`.
No commutativity assumption on `R` is required. -/
def sheafOfModulesDGNerveHomotopyCategoryEquiv [HasDerivedCategory (SheafOfModules.{u} R)] :
    (dgNerve (ULift.{u} ℤ)
      (FibrantInjectiveDGCategory (SheafOfModules.{u} R))).HomotopyCategory ≌
      DerivedCategory (SheafOfModules.{u} R) :=
  FibrantInjectiveDGCategory.dgNerveHomotopyCategoryEquiv.{u}
    (ULift.{u} ℤ) (SheafOfModules.{u} R)

/-- On a preorder site, restricting unbounded complexes of sheaves of modules to a lower interval
`Over U` preserves fibrations in the injective model structure. -/
theorem fibration_overFunctor_mapHomologicalComplex {P : Type u} [Preorder P]
    {J : GrothendieckTopology P} (R : Sheaf J RingCat.{u}) (U : P)
    {X Y : CochainComplex (SheafOfModules.{u} R) ℤ} (p : X ⟶ Y) [Fibration p] :
    Fibration (((SheafOfModules.overFunctor.{u} R U).mapHomologicalComplex (.up ℤ)).map p) := by
  let adj : SheafOfModules.pullback.{u} (F := Over.forget U) (𝟙 (R.over U)) ⊣
      SheafOfModules.overFunctor.{u} R U :=
    SheafOfModules.pullbackPushforwardAdjunction (F := Over.forget U) (𝟙 (R.over U))
  exact adj.fibration_mapHomologicalComplex_map p

/-- On a preorder site, restricting unbounded complexes of sheaves of modules to a lower interval
`Over U` sends fibrant injective complexes to fibrant injective complexes. -/
theorem isFibrant_overFunctor_mapHomologicalComplex {P : Type u} [Preorder P]
    {J : GrothendieckTopology P} (R : Sheaf J RingCat.{u}) (U : P)
    (X : CochainComplex (SheafOfModules.{u} R) ℤ) [IsFibrant X] :
    IsFibrant (((SheafOfModules.overFunctor.{u} R U).mapHomologicalComplex (.up ℤ)).obj X) := by
  let adj : SheafOfModules.pullback.{u} (F := Over.forget U) (𝟙 (R.over U)) ⊣
      SheafOfModules.overFunctor.{u} R U :=
    SheafOfModules.pullbackPushforwardAdjunction (F := Over.forget U) (𝟙 (R.over U))
  exact adj.isFibrant_mapHomologicalComplex_obj X

end SheafOfModules

section UnboundedCounterexample

/-- Every term of `UnboundedFlat.complex` (`⋯ → ℤ/4 --2--> ℤ/4 → ⋯`) is an injective object of
`ModuleCat (ZMod 4)`. -/
theorem injective_unboundedFlat_complex_X (n : ℤ) :
    Injective (UnboundedFlat.complex.X n) := by
  have : Module.Injective (ZMod 4) (ZMod 4) := (Module.Baer.zmod_self 4).injective
  exact Module.injective_object_of_injective_module (ZMod 4) (ZMod 4)

/-- The identity of `UnboundedFlat.complex` is not null-homotopic: in degree `0`, every chain
homotopy takes values in `2 • (ℤ/4)`, which does not contain `1`. -/
theorem not_nonempty_homotopy_id_zero_unboundedFlat_complex :
    ¬ Nonempty (Homotopy (𝟙 UnboundedFlat.complex) 0) := by
  rintro ⟨h⟩
  have hcomm := h.comm 0
  rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 from rfl),
    prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)] at hcomm
  have hd01 : (UnboundedFlat.complex.d 0 1).hom 1 = (2 : ZMod 4) := by
    simpa using alternatingMulRightComplex_d_apply (a := (2 : ZMod 4)) (b := 2)
      (by decide) (by decide) (rfl : (0 : ℤ) + 1 = 1) 1
  have hd10 : ∀ x : ZMod 4, (UnboundedFlat.complex.d (-1) 0).hom x = x * 2 := fun x ↦ by
    simpa using alternatingMulRightComplex_d_apply (a := (2 : ZMod 4)) (b := 2)
      (by decide) (by decide) (show (-1 : ℤ) + 1 = 0 by decide) x
  have h0 := congrArg (fun φ : UnboundedFlat.complex.X 0 ⟶ UnboundedFlat.complex.X 0 ↦
    φ.hom (1 : ZMod 4)) hcomm
  simp only [HomologicalComplex.id_f, HomologicalComplex.zero_f, add_zero,
    ModuleCat.hom_id, LinearMap.id_apply, ModuleCat.hom_add, LinearMap.add_apply,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, hd01, hd10] at h0
  have h2 : (h.hom 1 0).hom (2 : ZMod 4) = 2 * (h.hom 1 0).hom 1 := by
    simpa only [smul_eq_mul, mul_one] using map_smul (h.hom 1 0).hom (2 : ZMod 4) (1 : ZMod 4)
  rw [h2] at h0
  generalize (h.hom 1 0).hom 1 = a at h0
  generalize (h.hom 0 (-1)).hom 1 = b at h0
  revert a b h0
  decide

/-- Although `UnboundedFlat.complex` is acyclic and degreewise injective over `ℤ/4`, it is not
K-injective. -/
theorem not_isKInjective_unboundedFlat_complex : ¬ UnboundedFlat.complex.IsKInjective := fun hK ↦
  not_nonempty_homotopy_id_zero_unboundedFlat_complex
    ((CochainComplex.isKInjective_and_acyclic_iff_nonempty_homotopy_id_zero
      UnboundedFlat.complex).1 ⟨hK, UnboundedFlat.acyclic_complex⟩)

/-- An unbounded complex of injective objects need not be fibrant in
`CochainComplex.modelCategoryInjective`. -/
theorem not_isFibrant_unboundedFlat_complex : ¬ IsFibrant UnboundedFlat.complex := fun hF ↦
  not_isKInjective_unboundedFlat_complex
    ((CochainComplex.modelCategoryInjective.isFibrant_iff UnboundedFlat.complex).1 hF).2

/-- `UnboundedFlat.complex` is degreewise injective and acyclic, yet is not an injective object of
`CochainComplex (ModuleCat (ZMod 4)) ℤ`. -/
theorem not_injective_unboundedFlat_complex : ¬ Injective UnboundedFlat.complex := fun hI ↦
  not_nonempty_homotopy_id_zero_unboundedFlat_complex
    ((CochainComplex.injective_iff_nonempty_homotopy_id_zero UnboundedFlat.complex).1 hI).2

end UnboundedCounterexample

end TauCeti.Examples.ModelCategoryInjective
