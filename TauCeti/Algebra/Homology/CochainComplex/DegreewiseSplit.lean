/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.Splitting
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Functionals on a degreewise split short complex of cochain complexes of modules

Let `S` be a short complex of cochain complexes of `A`-modules, with chosen splittings of the
degreewise short complexes `S.X₁ n ⟶ S.X₂ n ⟶ S.X₃ n`. The splittings need not commute with the
differentials. This file records how an `A`-linear functional on a term of the middle complex
which kills the image of the differential restricts along the inclusion `S.f`, is corrected by a
primitive composed with the retraction, and descends along the section to the third complex.
These are the elementary steps in the proof that the dual of the middle complex is exact when
the duals of the outer complexes are.

## Main results

* `CategoryTheory.ShortComplex.comp_f_comp_d_eq_zero`: restriction to the first complex preserves
  killing the image of the differential.
* `CategoryTheory.ShortComplex.residual_comp_f_eq_zero`: the residual functional `φ - ψ₁ ∘ r ∘ d`
  vanishes on the first complex.
* `CategoryTheory.ShortComplex.residual_comp_d_eq_zero`: subtracting a functional of the form
  `ψ₀ ∘ d` preserves killing the image of the differential.
* `CategoryTheory.ShortComplex.comp_s_comp_d_eq_zero`: a functional vanishing on the first complex
  and on the image of the differential descends along the section to the third complex.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.ShortComplex

variable {A : Type u} [Ring A] {S : ShortComplex (CochainComplex (ModuleCat.{v} A) ℤ)}

/-- Restricting a functional that kills the image of the middle differential to the first complex
along the inclusion gives a functional that kills the image of the first differential. -/
theorem comp_f_comp_d_eq_zero {i j : ℤ} {φ : S.X₂.X j →ₗ[A] A}
    (hφ : φ.comp (S.X₂.d i j).hom = 0) :
    (φ.comp (S.f.f j).hom).comp (S.X₁.d i j).hom = 0 := by
  ext x
  have hx := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (S.f.comm i j)) x
  have hz := congrArg (fun f ↦ f ((S.f.f i).hom x)) hφ
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx ⊢
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
  simp only [LinearMap.zero_apply]
  rw [← hx, hz]

/-- The residual functional `φ - ψ₁ ∘ r ∘ d` vanishes on the first complex, where `ψ₁` is a
primitive of the restriction of `φ` to the first complex. -/
theorem residual_comp_f_eq_zero
    (s : ∀ n, (ShortComplex.mk (S.f.f n) (S.g.f n)
      (by rw [← HomologicalComplex.comp_f, S.zero, HomologicalComplex.zero_f])).Splitting)
    {j k : ℤ} {φ : S.X₂.X j →ₗ[A] A}
    {ψ₁ : S.X₁.X k →ₗ[A] A}
    (hψ₁ : ψ₁.comp (S.X₁.d j k).hom = φ.comp (S.f.f j).hom) :
    (φ - (ψ₁.comp (s k).r.hom).comp (S.X₂.d j k).hom).comp (S.f.f j).hom = 0 := by
  ext x
  have hx := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (S.f.comm j k)) x
  have hrx := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (s k).f_r) ((S.X₁.d j k).hom x)
  have hrx' : (s k).r.hom ((S.f.f k).hom ((S.X₁.d j k).hom x)) = (S.X₁.d j k).hom x := by
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
      LinearMap.id_apply] using hrx
  have hψx := LinearMap.congr_fun hψ₁ x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, ModuleCat.hom_comp,
    LinearMap.zero_apply] at hx hψx ⊢
  rw [hx, hrx', hψx]
  simp

/-- Subtracting a functional of the form `ψ₀ ∘ d` from one killing the image of the middle
differential into degree `j` keeps it killing that image, as `d ∘ d = 0`. -/
theorem residual_comp_d_eq_zero {i j k : ℤ} {φ : S.X₂.X j →ₗ[A] A}
    (hφ : φ.comp (S.X₂.d i j).hom = 0) (ψ₀ : S.X₂.X k →ₗ[A] A) :
    (φ - ψ₀.comp (S.X₂.d j k).hom).comp (S.X₂.d i j).hom = 0 := by
  ext x
  have hdx := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (S.X₂.d_comp_d i j k)) x
  have hφx := congrArg (fun f ↦ f x) hφ
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, ModuleCat.hom_comp, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hdx hφx ⊢
  rw [hφx, hdx]
  simp

/-- A functional on the middle complex that vanishes on the first complex and on the image of the
differential into degree `j` descends along the section to a functional on the third complex that
vanishes on the image of its differential. -/
theorem comp_s_comp_d_eq_zero
    (s : ∀ n, (ShortComplex.mk (S.f.f n) (S.g.f n)
      (by rw [← HomologicalComplex.comp_f, S.zero, HomologicalComplex.zero_f])).Splitting)
    {i j : ℤ} {ρ : S.X₂.X j →ₗ[A] A}
    (hρf : ρ.comp (S.f.f j).hom = 0) (hρ : ρ.comp (S.X₂.d i j).hom = 0) :
    (ρ.comp (s j).s.hom).comp (S.X₃.d i j).hom = 0 := by
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (S.g.comm i j)) ((s i).s.hom x)
  have hsx := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (s i).s_g) x
  have hsx' : (S.g.f i).hom ((s i).s.hom x) = x := by
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
      LinearMap.id_apply] using hsx
  have hz := LinearMap.congr_fun hρ ((s i).s.hom x)
  have hx' : (S.X₃.d i j).hom ((S.g.f i).hom ((s i).s.hom x)) =
      (S.g.f j).hom ((S.X₂.d i j).hom ((s i).s.hom x)) := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hx
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz ⊢
  rw [← hsx', hx']
  have hρ_eqx := LinearMap.congr_fun ((s j).comp_s_hom_comp_g_hom_of_comp_f_hom_eq_zero ρ hρf)
    ((S.X₂.d i j).hom ((s i).s.hom x))
  simpa only [LinearMap.comp_apply] using hρ_eqx.trans hz

end CategoryTheory.ShortComplex
