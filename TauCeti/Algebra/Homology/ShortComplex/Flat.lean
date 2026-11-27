/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Tensoring short exact sequences of modules with flat third term

If `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is a short exact sequence of modules over a commutative ring `R` and
`X₃` is flat, then tensoring on either side with any `R`-module preserves short exactness:
tensoring is right exact, and flatness of `X₃` preserves injectivity of `X₁ ⟶ X₂`
(`LinearMap.lTensor_injective_of_exact_of_flat`).

## Main results

* `CategoryTheory.ShortComplex.ShortExact.lTensor_of_flat`: tensoring a short exact sequence with
  flat third term on the left with any `R`-module (in an arbitrary universe) is short exact.
* `CategoryTheory.ShortComplex.ShortExact.map_tensorLeft_of_flat`: applying `tensorLeft M` to a
  short exact sequence in `ModuleCat R` with flat third term preserves short exactness.
* `CategoryTheory.ShortComplex.ShortExact.map_tensorRight_of_flat`: applying `tensorRight M` to a
  short exact sequence in `ModuleCat R` with flat third term preserves short exactness.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u v w

namespace CategoryTheory.ShortComplex.ShortExact

/-- Tensoring a short exact sequence of `R`-modules with flat third term on the left with any
`R`-module `Q` yields a short exact sequence of `R`-modules. -/
theorem lTensor_of_flat {R : Type u} [CommRing R] {X : ShortComplex (ModuleCat.{w} R)}
    (hX : X.ShortExact) [Module.Flat R X.X₃] (Q : Type v) [AddCommGroup Q] [Module R Q] :
    (ShortComplex.mk (ModuleCat.ofHom (X.f.hom.lTensor Q)) (ModuleCat.ofHom (X.g.hom.lTensor Q))
      (by ext; simp)).ShortExact := by
  have hg := (ModuleCat.epi_iff_surjective _).1 hX.epi_g
  have hfg := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hX.exact
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact lTensor_exact Q hfg hg
  · rw [ModuleCat.mono_iff_injective]
    exact LinearMap.lTensor_injective_of_exact_of_flat X.g.hom hg X.f.hom
      hX.moduleCat_injective_f hfg Q
  · rw [ModuleCat.epi_iff_surjective]
    exact LinearMap.lTensor_surjective Q hg

/-- Tensoring a short exact sequence of `R`-modules with flat third term on the left with any
`R`-module `M` preserves short exactness. -/
theorem map_tensorLeft_of_flat {R : Type u} [CommRing R] {X : ShortComplex (ModuleCat.{u} R)}
    (hX : X.ShortExact) [Module.Flat R X.X₃] (M : ModuleCat.{u} R) :
    (X.map (tensorLeft M)).ShortExact :=
  ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by ext; simp [ModuleCat.hom_whiskerLeft])
      (by ext; simp [ModuleCat.hom_whiskerLeft]))
    (hX.lTensor_of_flat M)

/-- Tensoring a short exact sequence of `R`-modules with flat third term on the right with any
`R`-module `M` preserves short exactness. -/
theorem map_tensorRight_of_flat {R : Type u} [CommRing R] {X : ShortComplex (ModuleCat.{u} R)}
    (hX : X.ShortExact) [Module.Flat R X.X₃] (M : ModuleCat.{u} R) :
    (X.map (tensorRight M)).ShortExact :=
  ShortComplex.shortExact_of_iso (X.mapNatIso (BraidedCategory.tensorLeftIsoTensorRight M))
    (hX.map_tensorLeft_of_flat M)

end CategoryTheory.ShortComplex.ShortExact
