/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Fiber
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.ZeroLocus
public import TauCeti.AlgebraicGeometry.IdealSheaf.Pullback
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.LineBundle.Image
import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Image

/-!
# Relative zero divisors of line-bundle functionals

A functional on an invertible sheaf on a flat family locally of finite presentation defines a
relative effective Cartier divisor when its pullback to each residue-field fibre is injective.
For integral fibres, it suffices that the pulled-back functional is nonzero.
The ideal is the image of the functional, and its formation commutes with arbitrary base change.
The flatness of the zero subscheme over the base follows from the fibrewise regular equations.

## References

* The Stacks Project, *Divisors*, Sections 31.14 and 31.18.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory
open Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

noncomputable section

variable {S X : Scheme.{u}} (L : InvertibleSheaf X) (f : X ⟶ S)
  [Flat f] [LocallyOfFinitePresentation f] (φ : L.obj ⟶ 𝟙_ X.Modules)

/-- A functional on a line bundle on a flat family locally of finite presentation defines a
relative effective Cartier divisor if its pullback to each residue-field fibre is injective. -/
theorem isRelativeEffectiveCartier_imageIdealSheaf_of_fiber_mono
    (hφ : ∀ s : S, Mono ((Scheme.Modules.pullback (f.fiberι s)).map φ ≫
      (Scheme.Modules.pullbackObjUnitIso (f.fiberι s)).hom)) :
    φ.imageIdealSheaf.IsRelativeEffectiveCartier f := by
  apply isRelativeEffectiveCartier_of_locallyPrincipal_of_forall_isEffectiveCartier_comap_fiberι
      φ.exists_imageIdealSheaf_ideal_eq_span
  intro s
  rw [← Scheme.Modules.Hom.imageIdealSheaf_pullback]
  exact @isEffectiveCartier_imageIdealSheaf _ ((pullback (f.fiberι s)).obj L) _ (hφ s)

/-- A functional on a line bundle on a flat family locally of finite presentation defines a
relative effective Cartier divisor when it is nonzero on every integral residue-field fibre. -/
theorem isRelativeEffectiveCartier_imageIdealSheaf_of_fiber_ne_zero
    (hintegral : ∀ s : S, IsIntegral (f.fiber s))
    (hφ : ∀ s : S, (Scheme.Modules.pullback (f.fiberι s)).map φ ≫
      (Scheme.Modules.pullbackObjUnitIso (f.fiberι s)).hom ≠ 0) :
    φ.imageIdealSheaf.IsRelativeEffectiveCartier f := by
  apply L.isRelativeEffectiveCartier_imageIdealSheaf_of_fiber_mono f φ
  intro s
  have := hintegral s
  let Ls : InvertibleSheaf (f.fiber s) :=
    ⟨(Scheme.Modules.pullback (f.fiberι s)).obj L.obj, inferInstance⟩
  let ψ : Ls.obj ⟶ 𝟙_ (f.fiber s).Modules :=
    (Scheme.Modules.pullback (f.fiberι s)).map φ ≫
      (Scheme.Modules.pullbackObjUnitIso (f.fiberι s)).hom
  exact Ls.mono_of_ne_zero_to_unit ψ (hφ s)

end

end TauCeti.AlgebraicGeometry.InvertibleSheaf
