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
One direction holds in any preadditive category with finite biproducts: a separator in `add M`
makes `M` a separator. For the other, the images of the morphisms `M ⟶ R` span a left ideal `τ`,
the trace of `M`, and the quotient map `R ⟶ R ⧸ τ` vanishes after composing with every morphism out
of `M`; so a separator `M` has `τ = R`. Since `1 ∈ τ` is a finite sum, finitely many morphisms
`M ⟶ R` already cover `R`, and the resulting `Mⁿ ⟶ R` splits. Categorically, `R` is a projective
object that is compact for directed unions of subobjects, and the quotient `R ⧸ τ` is again finitely
generated, although `τ` need not be: this is why no Noetherian hypothesis is needed.

The comparison with `TauCeti.Module.IsGenerator` holds for modules in any universe in which `R` is
small, with the regular module and `R ⧸ τ` replaced by their `Shrink`s; a generator is a separator
in every universe (`FGModuleCat.isSeparator_of_isGenerator`).

## Main results

* `FGModuleCat.isSeparator`: the regular module is a separator of `FGModuleCat R`.
* `FGModuleCat.isSeparator_iff_isGenerator`: the separators of `mod R` are the generators of the
  module category.
* `FGModuleCat.isSeparator_of_isGenerator`: a generator is a separator, in any universe.
* `FGModuleCat.additiveClosure_of_isGenerator_of_projective`: a finitely generated projective
  module lies in the additive closure `add M` of every finitely generated generator `M`, in any
  universe.
* `FGModuleCat.isSeparator_iff_additiveClosure` and `FGModuleCat.isSeparator_iff_exists_retract`:
  `M` is a separator of `mod R` exactly when `R ∈ add M`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v

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

/-- **The regular module lies in the additive closure of a generator**: if `M` is a generator of
the module category, then the regular module lies in `add M`. -/
theorem _root_.FGModuleCat.additiveClosure_of_isGenerator (M : FGModuleCat.{u} R)
    [Module.IsGenerator R M] : additiveClosure M (FGModuleCat.of R R) := by
  -- If `∑ᵢ φᵢ(mᵢ) = 1`, the maps `r ↦ r • mᵢ` and `φᵢ` exhibit `R` as a retract of `Mⁿ`.
  obtain ⟨n, φ, m, h⟩ := Module.IsGenerator.exists_sum_eq_one (R := R) (M := M)
  refine additiveClosure_iff_exists_sum_comp_eq_id.2
    ⟨n, fun i ↦ ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (m i))),
      fun i ↦ ObjectProperty.homMk (ModuleCat.ofHom (φ i)), ?_⟩
  apply (ObjectProperty.ι _).map_injective
  rw [Functor.map_sum, CategoryTheory.Functor.map_id]
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  simpa using h

/-- **A generator of the module category is a separator of `mod R`**, in any universe of modules.
-/
theorem _root_.FGModuleCat.isSeparator_of_isGenerator (M : FGModuleCat.{v} R)
    [Module.IsGenerator R M] : IsSeparator M := by
  refine (Preadditive.isSeparator_iff _).2 fun X Y f hf ↦ ?_
  -- `f` vanishes on the image of every morphism `M ⟶ X`, and these images span `X`.
  have h : ⨆ g : M →ₗ[R] X, LinearMap.range g ≤ LinearMap.ker f.hom.hom :=
    iSup_le fun g ↦ LinearMap.range_le_ker_iff.2 <|
      congr(($(hf (ObjectProperty.homMk (ModuleCat.ofHom g)))).hom.hom)
  rw [Module.IsGenerator.iSup_range_eq_top, top_le_iff, LinearMap.ker_eq_top] at h
  exact ObjectProperty.hom_ext _ (ModuleCat.hom_ext h)

/-- **A separator of `mod R` is a generator of the module category**: the trace of `M`, spanned by
the images of the linear forms on `M`, is all of `R`. The modules may live in any universe in which
`R` is small. -/
theorem _root_.FGModuleCat.isGenerator_of_isSeparator [Small.{v} R] {M : FGModuleCat.{v} R}
    (hM : IsSeparator M) : Module.IsGenerator R M := by
  rw [Module.isGenerator_iff_iSup_range_eq_top]
  set τ := ⨆ φ : M →ₗ[R] R, LinearMap.range φ
  have : Small.{v} (R ⧸ τ) := small_of_surjective τ.mkQ_surjective
  let e := Shrink.linearEquiv.{v} R R
  let e' := Shrink.linearEquiv.{v} R (R ⧸ τ)
  -- The quotient map `R ⟶ R ⧸ τ`, transported to the universe `v`, vanishes on every `M ⟶ R`.
  let π : FGModuleCat.of R (Shrink.{v} R) ⟶ FGModuleCat.of R (Shrink.{v} (R ⧸ τ)) :=
    FGModuleCat.ofHom (e'.symm.toLinearMap ∘ₗ τ.mkQ ∘ₗ e.toLinearMap)
  have hπ : π = 0 := (Preadditive.isSeparator_iff _).1 hM π fun g ↦ by
    refine ObjectProperty.hom_ext _ (ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
    simpa [π, ObjectProperty.FullSubcategory.comp_hom] using Submodule.mem_iSup_of_mem
      (e.toLinearMap ∘ₗ g.hom.hom) (LinearMap.mem_range_self (e.toLinearMap ∘ₗ g.hom.hom) x)
  refine eq_top_iff.2 fun r _ ↦ (Submodule.Quotient.mk_eq_zero τ).1 (e'.symm.map_eq_zero_iff.1 ?_)
  simpa [π] using congr(($hπ).hom.hom (e.symm r))

/-- **The separators of `mod R` are the generators of the module category**, in any universe of
modules in which `R` is small. -/
theorem _root_.FGModuleCat.isSeparator_iff_isGenerator [Small.{v} R] (M : FGModuleCat.{v} R) :
    IsSeparator M ↔ Module.IsGenerator R M :=
  ⟨FGModuleCat.isGenerator_of_isSeparator, fun _ ↦ FGModuleCat.isSeparator_of_isGenerator M⟩

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

/-- **Finitely generated projective modules are summands of finite sums of a generator**: if `M`
is a generator of the module category, then a projective object of `FGModuleCat R` lies in `add M`.
The modules may live in any universe. -/
theorem _root_.FGModuleCat.additiveClosure_of_isGenerator_of_projective (M P : FGModuleCat.{v} R)
    [Module.IsGenerator R M] [Projective P] : additiveClosure M P := by
  -- If `∑ᵢ φᵢ(mᵢ) = 1` and the `xⱼ` generate `P`, the maps `m ↦ φᵢ(m) • xⱼ` give an epimorphism
  -- from a finite sum of copies of `M`, which splits since `P` is projective.
  obtain ⟨n, φ, m, h⟩ := Module.IsGenerator.exists_sum_eq_one (R := R) (M := M)
  obtain ⟨k, x, hx⟩ := Module.Finite.exists_fin (R := R) (M := P)
  let p : (⨁ fun _ : Fin k × Fin n ↦ M) ⟶ P := biproduct.desc fun j ↦
    ObjectProperty.homMk (ModuleCat.ofHom ((φ j.2).smulRight (x j.1)))
  have : Epi p := Preadditive.epi_of_cancel_zero p fun {Z} g hg ↦ by
    refine ObjectProperty.hom_ext _ (ModuleCat.hom_ext (LinearMap.ext_on_range hx fun j ↦ ?_))
    have hj (i : Fin n) : φ i (m i) • g.hom.hom (x j) = 0 := by
      simpa [p] using congr((biproduct.ι _ (j, i) ≫ $hg).hom.hom (m i))
    have : ∑ i, φ i (m i) • g.hom.hom (x j) = 0 := Finset.sum_eq_zero fun i _ ↦ hj i
    simpa [← Finset.sum_smul, h] using this
  exact (additiveClosure M).prop_of_retract ⟨Projective.factorThru (𝟙 P) p, p, by simp⟩
    ((additiveClosure M).prop_of_isLimit (biproduct.isLimit _) fun _ ↦ additiveClosure_self M)

end TauCeti
