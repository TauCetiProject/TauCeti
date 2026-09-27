/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Scalar extension of endomorphisms of finitely generated modules

Extension of scalars carries multiplication by a scalar to multiplication by its image.
This transports the curvature equations of a matrix factorization when its components are
extended along a ring map, so the resulting factorization has the image potential.
-/

public section

universe u v

namespace TauCeti.ModuleCat

open CategoryTheory
open scoped ChangeOfRings

variable {S : Type u} {T : Type v} [CommRing S] [CommRing T] {w : S}

/-- Scalar extension sends multiplication by a scalar to multiplication by its image. -/
@[simp] theorem extendScalars_map_smul_id (f : S →+* T) (M : _root_.ModuleCat.{u} S) :
    (_root_.ModuleCat.extendScalars f).map (w • 𝟙 M) = f w • 𝟙 _ := by
  apply _root_.ModuleCat.ExtendScalars.hom_ext
  intro m
  let _ : Algebra S T := f.toAlgebra
  -- The category map hides the tensor-product representative, so expose it here.
  change (1 : T) ⊗ₜ[S,f] (w • m) = (f w) • ((1 : T) ⊗ₜ[S,f] m)
  rw [← TensorProduct.smul_tmul]
  -- `f` defines the `S`-action on `T`, so both tensor representatives now reduce to
  -- the same multiplication in `T`.
  change (f w * 1 : T) ⊗ₜ[S,f] m = (f w * 1 : T) ⊗ₜ[S,f] m
  rfl

end TauCeti.ModuleCat
