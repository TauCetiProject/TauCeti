/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import TauCeti.AlgebraicGeometry.Modules.Localization
import TauCeti.AlgebraicGeometry.AffineScheme

/-!
# Locally bijective maps into quasi-coherent modules on affine opens

Let `X` be a scheme, `P` a presheaf of `𝒪_X`-modules and `M` a quasi-coherent `𝒪_X`-module. A
morphism `φ : P ⟶ M` which is locally injective and locally surjective (for instance the unit of
the sheafification of `P`, when `M` is the sheafification of `P`) need not be bijective on
sections. It is bijective on the sections over an affine open `U` as soon as the restrictions of
`P` from `U` to the basic opens `D(f) ⊆ U` are localizations at the powers of `f`, as they are
for `M` (`Scheme.Modules.isLocalizedModule_basicOpenRestrict`).

The input on the side of `U` is that a covering sieve of an affine open `U` contains the basic
opens `D(f)` for a family of functions `f` generating the unit ideal of `Γ(X, U)`
(`AlgebraicGeometry.IsAffineOpen.span_setOf_basicOpen_mem_sieve_eq_top`, in
`TauCeti.AlgebraicGeometry.AffineScheme`); bijectivity then follows by clearing denominators, as in
Hartshorne, Lemma II.5.3.

This computes the sections over affine opens of sheaves obtained by sheafifying a sectionwise
construction on a quasi-coherent module, such as its symmetric powers.

## Main declarations

* `AlgebraicGeometry.IsAffineOpen.bijective_app_of_isLocalizedModule`: a locally bijective morphism
  from a presheaf of modules whose restrictions to basic opens are localizations into a
  quasi-coherent module is bijective on sections over affine opens.

## References

* R. Hartshorne, *Algebraic Geometry*, Lemma II.5.3.
-/

public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.IsAffineOpen

variable {X : Scheme.{u}} {U : X.Opens}

variable {P : PresheafOfModulesOfCommRing.{u} X.presheaf} {M : X.Modules}

/-- **Locally bijective maps into a quasi-coherent module are bijective on affine opens.** Let
`φ : P ⟶ M` be a locally injective and locally surjective morphism from a presheaf of
`𝒪_X`-modules to a quasi-coherent `𝒪_X`-module, and let `U` be an affine open such that the
restrictions of `P` from `U` to the basic opens `D(f) ⊆ U` are localizations at the powers of
`f`. Then `φ` is bijective on sections over `U`. -/
theorem bijective_app_of_isLocalizedModule (hU : IsAffineOpen U) [M.IsQuasicoherent]
    (φ : P ⟶ M.val)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map φ)]
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map φ)]
    (hP : ∀ f : Γ(X, U),
      IsLocalizedModule (.powers f) (P.map (homOfLE (X.basicOpen_le f)).op).hom) :
    Function.Bijective (φ.app (op U)) := by
  let J := Opens.grothendieckTopology X
  refine ⟨fun a b hab ↦ ?_, fun s ↦ ?_⟩
  · -- `a - b` vanishes on basic opens `D(f)` with `f` generating the unit ideal, so it is
    -- killed by a power of each such `f`.
    have hS := Presheaf.equalizerSieve_mem J ((PresheafOfModules.toPresheaf _).map φ) a b hab
    rw [← sub_eq_zero]
    refine (Submodule.mem_bot Γ(X, U)).1 (Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _
      (hU.span_setOf_basicOpen_mem_sieve_eq_top hS) _ fun ⟨f, hf⟩ ↦ ?_)
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (hP f).exists_of_eq (x₁ := a) (x₂ := b) hf
    exact ⟨n, by simpa [Submonoid.smul_def, smul_sub, sub_eq_zero] using hn⟩
  · -- `s` lies in the image of `φ` on basic opens `D(f)` with `f` generating the unit ideal,
    -- and a power of each such `f` multiplies `s` into the image of `φ` over `U`.
    have hS := Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map φ) s
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem
      (LinearMap.range (PresheafOfModules.Hom.app' φ (op U)).hom) _
      (hU.span_setOf_basicOpen_mem_sieve_eq_top hS) s fun ⟨f, b, hb⟩ ↦ ?_
    obtain ⟨⟨a, _, k, rfl⟩, hak⟩ := (hP f).surj b
    let i : X.basicOpen f ⟶ U := homOfLE (X.basicOpen_le f)
    -- `φ (a|_{D(f)}) = f ^ k • φ b = (f ^ k • s)|_{D(f)}`, so `φ a - f ^ k • s` vanishes on `D(f)`.
    have key : M.presheaf.map i.op (φ.app (op U) a - f ^ k • s) = 0 := by
      -- `rw` cannot rewrite here (the motive mixes `M.presheaf` with `M.val` and the sections of
      -- `toPresheaf`), so each step is a term: naturality of `φ`, `hak`, linearity of `φ`, `hb`
      -- and linearity of the restriction of `M`.
      refine (map_sub _ _ _).trans (sub_eq_zero.2 ?_)
      refine (PresheafOfModules.naturality_apply φ i.op a).symm.trans ?_
      refine (congrArg (φ.app (op (X.basicOpen f))) hak.symm).trans ?_
      refine ((φ.app (op (X.basicOpen f))).hom.map_smul _ b).trans ?_
      refine (congrArg _ hb).trans ?_
      exact (M.map_smul i (f ^ k) s).symm
    obtain ⟨m, hm⟩ := M.exists_pow_smul_eq_zero_of_isCompact hU.isCompact f
      (φ.app (op U) a - f ^ k • s) ((M.basicOpenRestrict_apply f _).trans key)
    refine ⟨m + k, f ^ m • a, ?_⟩
    refine ((PresheafOfModules.Hom.app' φ (op U)).hom.map_smul _ a).trans ?_
    rw [pow_add, mul_smul]
    exact sub_eq_zero.1 ((smul_sub _ _ _).symm.trans hm)

end AlgebraicGeometry.IsAffineOpen
