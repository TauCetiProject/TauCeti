/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Classification
public import TauCeti.AlgebraicGeometry.Curves.Category

/-!
# Morphisms of regular proper curves from function-field embeddings

For regular proper curves `X` and `Y` over a field `k`, a `k`-embedding
`φ : k(Y) → k(X)` determines a unique dominant `k`-morphism `X ⟶ Y`. The local rings of `X`
are valuation rings and `Y` is proper, so the morphism through the generic point extends to `X`.

`RegularProperCurveCat.homOfAlgHom` constructs this morphism for arbitrary regular proper curves.
The lemmas `functionFieldAlgHom_homOfAlgHom` and `homOfAlgHom_functionFieldAlgHom` show that this
construction and pullback of rational functions are inverse. The two-chart model construction and
anti-equivalence are in `TauCeti.AlgebraicGeometry.Curves.TwoChartModel.AntiEquivalence`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Corollary I.6.12.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002, Section 7.3.
-/

public section

open CategoryTheory Opposite _root_.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable (k : Type u) [Field k]

namespace RegularProperCurveCat

variable {k}
variable {X Y Z : RegularProperCurveCat k}

/-! ### Morphisms from embeddings of function fields -/

/-- **The morphism of regular proper curves induced by a `k`-embedding** `φ : k(Y) → k(X)` of
function fields: the unique dominant `k`-morphism `X ⟶ Y` whose pullback of rational functions is
`φ` (`functionFieldAlgHom_homOfAlgHom`, `homOfAlgHom_functionFieldAlgHom`). -/
noncomputable def homOfAlgHom (φ : Y.toScheme.functionField →ₐ[k] X.toScheme.functionField) :
    X ⟶ Y :=
  haveI hX := Scheme.IsCurveOver.valuationRing_stalk k X.toScheme
  haveI hφ := Scheme.specMap_comp_fromSpecStalk_genericPoint_comp_over k
    (CommRingCat.ofHom φ.toRingHom) φ.commutes
  { hom := Scheme.homOfFunctionField hX _ hφ
    isOver := Scheme.isOver_homOfFunctionField hX _ hφ
    isDominant := Scheme.Hom.isDominant_of_SpecMap_fromSpecStalk _ _
      (Scheme.fromSpecStalk_homOfFunctionField hX _ hφ).symm }

/-- **The pullback of rational functions along `homOfAlgHom φ` is `φ`.** -/
@[simp]
theorem functionFieldAlgHom_homOfAlgHom
    (φ : Y.toScheme.functionField →ₐ[k] X.toScheme.functionField) :
    (homOfAlgHom φ).hom.functionFieldAlgHom k = φ := by
  have hX := Scheme.IsCurveOver.valuationRing_stalk k X.toScheme
  have h := ((Scheme.Hom.eq_functionFieldMap_iff (homOfAlgHom φ).hom
    (CommRingCat.ofHom φ.toRingHom)).mpr
    (Scheme.fromSpecStalk_homOfFunctionField hX _ _).symm).symm
  ext x
  rw [Scheme.Hom.functionFieldAlgHom_apply]
  exact congr($h x)

/-- **A dominant `k`-morphism is induced by its pullback of rational functions**: `f : X ⟶ Y` is
`homOfAlgHom` of `f^* : k(Y) → k(X)`. -/
@[simp]
theorem homOfAlgHom_functionFieldAlgHom (f : X ⟶ Y) :
    homOfAlgHom (f.hom.functionFieldAlgHom k) = f := by
  refine hom_ext (Scheme.Hom.ext_of_functionFieldMap_eq (Spec (.of k)) ?_)
  ext z
  have h := DFunLike.congr_fun (functionFieldAlgHom_homOfAlgHom (f.hom.functionFieldAlgHom k)) z
  rwa [Scheme.Hom.functionFieldAlgHom_apply, Scheme.Hom.functionFieldAlgHom_apply] at h

/-- A dominant `k`-morphism of regular proper curves is determined by its pullback of rational
functions. -/
theorem functionFieldAlgHom_injective :
    Function.Injective fun f : X ⟶ Y ↦ f.hom.functionFieldAlgHom k := fun f g h ↦ by
  rw [← homOfAlgHom_functionFieldAlgHom f, ← homOfAlgHom_functionFieldAlgHom g]
  exact congrArg homOfAlgHom h

end RegularProperCurveCat

end TauCeti.AlgebraicGeometry
