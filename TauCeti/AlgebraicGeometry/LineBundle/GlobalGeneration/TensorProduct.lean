/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Presentation
public import TauCeti.CategoryTheory.Monoidal.Closed.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Pullback
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.LineBundle.TensorProduct

/-!
# Global generation of tensor products and tensor powers

The tensor product of two globally generated line bundles is globally generated, and so is every
tensor power `L^{⊗n}` of a globally generated line bundle `L`. The proof goes through Mathlib's
`SheafOfModules.GeneratingSections`: if `𝒪_X^{(I)} ⟶ L` and `𝒪_X^{(J)} ⟶ K` are epimorphisms, then
so is their tensor product (`CategoryTheory.MonoidalClosed.epi_tensorHom`, as `𝒪_X`-modules form
a braided closed monoidal category), whose source is the free sheaf `𝒪_X^{(I × J)}`
(`TauCeti.SheafOfModules.freeTensorFreeIso`).

## Main results

* `TauCeti.AlgebraicGeometry.InvertibleSheaf.IsGloballyGenerated.tensorProduct`: `L ⊗ K` is
  globally generated when `L` and `K` are;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.IsGloballyGenerated.tensorPow`: `L^{⊗n}` is globally
  generated when `L` is.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 7.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

variable {X : Scheme.{u}}

/-- The tensor product of two globally generated line bundles is globally generated: products
of generating sections generate the tensor product. -/
theorem IsGloballyGenerated.tensorProduct {L K : InvertibleSheaf X} (hL : L.IsGloballyGenerated)
    (hK : K.IsGloballyGenerated) : (L.tensorProduct K).IsGloballyGenerated := by
  obtain ⟨σ⟩ := isGloballyGenerated_iff_nonempty_generatingSections.mp hL
  obtain ⟨τ⟩ := isGloballyGenerated_iff_nonempty_generatingSections.mp hK
  -- The free sheaves are read in the monoidal category `X.Modules`, where the tensor product of
  -- the generating morphisms lives.
  let e : (SheafOfModules.free σ.I ⊗ SheafOfModules.free τ.I : X.Modules) ≅
      SheafOfModules.free (σ.I × τ.I) :=
    TauCeti.SheafOfModules.freeTensorFreeIso σ.I τ.I
  let p : (SheafOfModules.free (σ.I × τ.I) : X.Modules) ⟶ (L.tensorProduct K).obj :=
    e.inv ≫ tensorHom (C := X.Modules) σ.π τ.π ≫ (tensorProductObjIso L K).inv
  -- The generating morphisms are epimorphisms of sheaves of modules; they are restated in
  -- `X.Modules`, whose braided closed monoidal structure gives the epimorphism `σ.π ⊗ τ.π`.
  have : Epi (C := X.Modules) σ.π := σ.epi
  have : Epi (C := X.Modules) τ.π := τ.epi
  have := MonoidalClosed.epi_tensorHom (C := X.Modules) σ.π τ.π
  -- The comparison isomorphisms live in the scheme-module category, so their epimorphism
  -- instances are supplied explicitly.
  have : Epi p := epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv e))
    (epi_comp' this (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)))
  exact isGloballyGenerated_iff_nonempty_generatingSections.mpr
    ⟨(SheafOfModules.free.generatingSections (σ.I × τ.I)).ofEpi p⟩

/-- Every tensor power of a globally generated line bundle is globally generated. -/
theorem IsGloballyGenerated.tensorPow {L : InvertibleSheaf X} (hL : L.IsGloballyGenerated)
    (n : ℕ) : (L.tensorPow n).IsGloballyGenerated := by
  induction n with
  | zero => exact L.tensorPow_zero ▸ isGloballyGenerated_trivial X
  | succ n ih => exact L.tensorPow_succ n ▸ ih.tensorProduct hL

end TauCeti.AlgebraicGeometry.InvertibleSheaf
