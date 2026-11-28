/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Right exactness of pullback of modules

For a morphism of schemes `f : Y ⟶ X`, the pullback `f^*` of modules is a left adjoint, so it
preserves cokernels and hence right exact sequences: an exact sequence `F' ⟶ F ⟶ F''` of
`𝒪_X`-modules whose second map is an epimorphism goes to an exact sequence of `𝒪_Y`-modules.
Pullback along a flat morphism is moreover exact
(`AlgebraicGeometry.Scheme.Modules.preservesHomology_pullback_of_flat`).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.exact_map_pullback`: pullback of modules along a morphism of
  schemes preserves right exact sequences.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **Pullback is right exact.** For a morphism of schemes `f : Y ⟶ X`, the pullback `f^*` of
modules carries an exact sequence `F' ⟶ F ⟶ F''` of `𝒪_X`-modules whose second map is an
epimorphism to an exact sequence of `𝒪_Y`-modules, since `f^*` is a left adjoint and so preserves
cokernels. -/
theorem exact_map_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) {K : ShortComplex X.Modules}
    (hK : K.Exact) [Epi K.g] : (K.map (pullback f)).Exact :=
  hK.map_of_epi_of_preservesCokernel _ inferInstance inferInstance

end AlgebraicGeometry.Scheme.Modules
