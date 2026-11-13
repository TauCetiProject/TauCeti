/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.Generator.Preadditive
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Module.Generator
public import TauCeti.CategoryTheory.Generator.GeneratorCogenerator

/-!
# Separators of finitely generated modules

The regular module detects morphisms of finitely generated modules: a morphism vanishes when its
composite with every morphism out of the regular module does. This is the analogue for
`FGModuleCat R` of Mathlib's `ModuleCat.isSeparator`.

Over any ring `R`, a finitely generated module `M` is a separator of `mod R = FGModuleCat R` exactly
when `R` is a direct summand of a finite sum `Mⁿ`, that is, `R ∈ add M`
(`FGModuleCat.isSeparator_iff_exists_retract`), exactly when `M` is a generator of the module
category in the sense of `TauCeti.Module.IsGenerator` (`FGModuleCat.isSeparator_iff_isGenerator`).
One direction holds in any preadditive category: a separator in `add M` makes `M` a separator. For
the other, the images of the morphisms `M ⟶ R` span a left ideal `τ`, the trace of `M`, and the
quotient map `R ⟶ R ⧸ τ` vanishes after composing with every morphism out of `M`; so a separator
`M` has `τ = R`. Since `1 ∈ τ` is a finite sum, finitely many morphisms `M ⟶ R` already cover `R`,
and the resulting `Mⁿ ⟶ R` splits. Categorically, `R` is a projective object that is compact for
directed unions of subobjects, and the quotient `R ⧸ τ` is again finitely generated, although `τ`
need not be: this is why no Noetherian hypothesis is needed.

## Main results

* `FGModuleCat.isSeparator`: the regular module is a separator of `FGModuleCat R`.
* `FGModuleCat.isSeparator_iff_isGenerator`: the separators of `mod R` are the generators of the
  module category.
* `FGModuleCat.isSeparator_iff_additiveClosure` and `FGModuleCat.isSeparator_iff_exists_retract`:
  `M` is a separator of `mod R` exactly when `R ∈ add M`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [Ring R]

/-- The regular module is a separator of the finitely generated modules, the analogue of Mathlib's
`ModuleCat.isSeparator`: a morphism vanishes when its composite with every morphism out of the
regular module does. -/
theorem _root_.FGModuleCat.isSeparator : IsSeparator (FGModuleCat.of R R) :=
  (Preadditive.isSeparator_iff _).mpr fun M N f h ↦ by
    ext x
    -- `ofHom` and composition unfold by definition, so the composite at `1` is `f (1 • x)`.
    have hx : f.hom.hom ((1 : R) • x) = 0 :=
      congrArg (fun g : FGModuleCat.of R R ⟶ N ↦ g.hom.hom 1)
        (h (FGModuleCat.ofHom (LinearMap.toSpanSingleton R M x)))
    simpa using hx

variable {R}

/-- **The regular module lies in the additive closure of a generator**: if `∑ᵢ φᵢ(mᵢ) = 1` for
linear forms `φᵢ` on `M` and vectors `mᵢ`, the maps `r ↦ r • mᵢ` and `φᵢ` exhibit `R` as a direct
summand of `Mⁿ`. -/
theorem _root_.FGModuleCat.additiveClosure_of_isGenerator (M : FGModuleCat.{u} R)
    [Module.IsGenerator R M] : additiveClosure M (FGModuleCat.of R R) := by
  obtain ⟨n, φ, m, h⟩ := Module.IsGenerator.exists_sum_eq_one (R := R) (M := M)
  refine additiveClosure_iff_exists_sum_comp_eq_id.2
    ⟨n, fun i ↦ ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (m i))),
      fun i ↦ ObjectProperty.homMk (ModuleCat.ofHom (φ i)), ?_⟩
  apply (ObjectProperty.ι _).map_injective
  rw [Functor.map_sum, CategoryTheory.Functor.map_id]
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  simpa using h

/-- **A separator of `mod R` is a generator of the module category**: the trace of `M`, spanned by
the images of the linear forms on `M`, is all of `R`. Otherwise the quotient map `R ⟶ R ⧸ τ` onto
the finitely generated module `R ⧸ τ` would be a nonzero morphism killed by every morphism out of
`M`. -/
theorem _root_.FGModuleCat.isGenerator_of_isSeparator {M : FGModuleCat.{u} R}
    (hM : IsSeparator M) : Module.IsGenerator R M := by
  rw [Module.isGenerator_iff_iSup_range_eq_top]
  set τ := ⨆ φ : M →ₗ[R] R, LinearMap.range φ
  let π : FGModuleCat.of R R ⟶ FGModuleCat.of R (R ⧸ τ) :=
    ObjectProperty.homMk (ModuleCat.ofHom τ.mkQ)
  have hπ : π = 0 := (Preadditive.isSeparator_iff _).1 hM π fun g ↦ by
    refine ObjectProperty.hom_ext _ (ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
    simpa [π, ObjectProperty.FullSubcategory.comp_hom] using
      Submodule.mem_iSup_of_mem g.hom.hom (LinearMap.mem_range_self g.hom.hom x)
  refine eq_top_iff.2 fun r _ ↦ (Submodule.Quotient.mk_eq_zero τ).1 ?_
  simpa [π] using congr(($hπ).hom.hom r)

/-- **The separators of `mod R` are the generators of the module category.** -/
theorem _root_.FGModuleCat.isSeparator_iff_isGenerator (M : FGModuleCat.{u} R) :
    IsSeparator M ↔ Module.IsGenerator R M :=
  ⟨FGModuleCat.isGenerator_of_isSeparator, fun _ ↦
    (FGModuleCat.isSeparator R).of_additiveClosure (FGModuleCat.additiveClosure_of_isGenerator M)⟩

/-- **The separators of `mod R`, through additive closures**: `M` is a separator of `mod R` exactly
when the regular module lies in `add M`. -/
theorem _root_.FGModuleCat.isSeparator_iff_additiveClosure (M : FGModuleCat.{u} R) :
    IsSeparator M ↔ additiveClosure M (FGModuleCat.of R R) :=
  ⟨fun h ↦ have := FGModuleCat.isGenerator_of_isSeparator h
    FGModuleCat.additiveClosure_of_isGenerator M,
    (FGModuleCat.isSeparator R).of_additiveClosure⟩

/-- Over any ring `R`, `M` is a separator of `mod R` exactly when the regular module is a direct
summand of a finite biproduct of copies of `M`, that is, `R ∈ add M`. -/
theorem _root_.FGModuleCat.isSeparator_iff_exists_retract (M : FGModuleCat.{u} R) :
    IsSeparator M ↔ ∃ n : ℕ, Nonempty (Retract (FGModuleCat.of R R) (⨁ fun _ : Fin n ↦ M)) :=
  (FGModuleCat.isSeparator_iff_additiveClosure M).trans additiveClosure_iff

end TauCeti
