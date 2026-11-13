/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Presentation
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.LineBundle.TensorProduct

/-!
# Global generation of tensor products and tensor powers

The tensor product of two globally generated line bundles is globally generated, and so is every
tensor power `L^{⊗n}` of a globally generated line bundle `L`. These closure properties apply to
`InvertibleSheaf.tensorProduct` and `InvertibleSheaf.tensorPow` and support the study of global
generation of ample twists `L^{⊗n} ⊗ K`.

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

/-- The tensor product of two globally generated line bundles is globally generated. -/
theorem IsGloballyGenerated.tensorProduct {L K : InvertibleSheaf X} (hL : L.IsGloballyGenerated)
    (hK : K.IsGloballyGenerated) : (L.tensorProduct K).IsGloballyGenerated := by
  obtain ⟨σ⟩ := isGloballyGenerated_iff_nonempty_generatingSections.mp hL
  obtain ⟨τ⟩ := isGloballyGenerated_iff_nonempty_generatingSections.mp hK
  -- Read the comparison in the category of sheaves of modules used by `GeneratingSections`.
  let e : (L.obj ⊗ K.obj : SheafOfModules X.ringCatSheaf) ≅ (L.tensorProduct K).obj :=
    (tensorProductObjIso L K).symm
  have : Epi e.hom := @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom e)
  exact isGloballyGenerated_iff_nonempty_generatingSections.mpr
    ⟨(σ.tensor (R := X.sheaf) τ).ofEpi e.hom⟩

/-- Every tensor power of a globally generated line bundle is globally generated. -/
theorem IsGloballyGenerated.tensorPow {L : InvertibleSheaf X} (hL : L.IsGloballyGenerated)
    (n : ℕ) : (L.tensorPow n).IsGloballyGenerated := by
  induction n with
  | zero => simp only [L.tensorPow_zero, isGloballyGenerated_trivial]
  | succ n ih => exact L.tensorPow_succ n ▸ ih.tensorProduct hL

end TauCeti.AlgebraicGeometry.InvertibleSheaf
