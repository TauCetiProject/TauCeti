/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The dual of a chain complex of modules

The dual `K∨` of a chain complex `K` of `R`-modules indexed by `ℤ` (`ChainComplex.linearDual`)
has in degree `p` the linear forms on `K_(-p)`, and differential `d f = (-1)^(p + 1) f ∘ d_K` on a
form `f` of degree `p` (`ChainComplex.linearDual_d_apply`). This is the sign convention
`d f = (-1)^(|f| + 1) f ∘ d` of the dual of a cochain complex (`CochainComplex.linearDual`,
`CochainComplex.linearDualXEquiv_d_apply`), in homological degrees. A morphism `φ : K ⟶ L` has the
transpose `ChainComplex.linearDualMap φ : L∨ ⟶ K∨`.

The terms of `K∨` are the dual modules themselves, so that their elements are linear forms. The
comparison with the dual of a cochain complex, through the regrading of chain complexes into
cochain complexes, is in `TauCeti.Algebra.Homology.LinearHomComplex.Regrade`.

## Main definitions

* `ChainComplex.linearDual`: the dual of a chain complex of modules.
* `ChainComplex.linearDualMap`: the transpose of a morphism of chain complexes.

## References

* C. A. Weibel, *An introduction to homological algebra*, Section 2.7, on Hom complexes and
  their sign conventions.
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex ComplexShape

universe u

namespace ChainComplex

variable {R : Type u} [CommRing R]

/-- The **dual complex** `K∨` of a chain complex `K` of `R`-modules: in degree `p` the linear
forms on `K_(-p)`, with differential `d f = (-1)^(p + 1) f ∘ d_K` on a form `f` of degree `p`.
It is an abbreviation whose terms are the dual modules themselves, so its elements are linear
forms (unlike `CochainComplex.linearDual`, whose terms are Hom-complex cochains identified with
forms by `CochainComplex.linearDualXEquiv`). -/
abbrev linearDual (K : ChainComplex (ModuleCat.{u} R) ℤ) : ChainComplex (ModuleCat.{u} R) ℤ where
  X p := ModuleCat.of R (Module.Dual R (K.X (-p)))
  d p q := (p + 1).negOnePow • ModuleCat.ofHom (K.d (-q) (-p)).hom.dualMap
  shape p q h := by
    rw [K.shape (-q) (-p) (by simp only [down_Rel] at h ⊢; omega)]
    ext f x
    simp [LinearMap.dualMap_apply]
  d_comp_d' p q r _ _ := by
    rw [Linear.units_smul_comp, Linear.comp_units_smul, ← ModuleCat.ofHom_comp,
      LinearMap.dualMap_comp_dualMap, ← ModuleCat.hom_comp, K.d_comp_d]
    ext f x
    simp [LinearMap.dualMap_apply]

variable {K : ChainComplex (ModuleCat.{u} R) ℤ}

/-- **The differential of the dual complex.** On a form `f` of degree `p`, the differential is
`d f = (-1)^(p + 1) f ∘ d_K`. -/
theorem linearDual_d_apply (p q : ℤ) (f : (linearDual K).X p) (x : K.X (-q)) :
    ((linearDual K).d p q).hom f x = (p + 1).negOnePow • f ((K.d (-q) (-p)).hom x) :=
  (rfl)

variable {L M : ChainComplex (ModuleCat.{u} R) ℤ}

/-- The transpose `L∨ ⟶ K∨` of a morphism of chain complexes `φ : K ⟶ L`. -/
def linearDualMap (φ : K ⟶ L) : linearDual L ⟶ linearDual K where
  f p := ModuleCat.ofHom (φ.f (-p)).hom.dualMap
  comm' p q _ := by
    ext f x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.dualMap_apply, ModuleCat.hom_smul, LinearMap.smul_apply]
    rw [← LinearMap.comp_apply (φ.f (-p)).hom, ← ModuleCat.hom_comp, ← φ.comm, ModuleCat.hom_comp,
      LinearMap.comp_apply]

/-- The transpose of `φ` sends a form `f` on `L_(-p)` to `f ∘ φ`. -/
@[simp]
theorem linearDualMap_f_apply (φ : K ⟶ L) (p : ℤ) (f : (linearDual L).X p) (x : K.X (-p)) :
    ((linearDualMap φ).f p).hom f x = f ((φ.f (-p)).hom x) :=
  (rfl)

/-- The transpose of the identity is the identity. -/
@[simp]
theorem linearDualMap_id : linearDualMap (𝟙 K) = 𝟙 _ :=
  (rfl)

/-- The transpose of a composite is the composite of the transposes, in the opposite order. -/
@[simp, reassoc]
theorem linearDualMap_comp (φ : K ⟶ L) (ψ : L ⟶ M) :
    linearDualMap (φ ≫ ψ) = linearDualMap ψ ≫ linearDualMap φ :=
  (rfl)

end ChainComplex
