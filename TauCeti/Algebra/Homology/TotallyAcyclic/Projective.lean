/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotallyAcyclic.Basic
public import Mathlib.RingTheory.Finiteness.Projective
public import TauCeti.LinearAlgebra.Finsupp.Supported

/-!
# Projective coefficients for complete resolutions

A totally acyclic complex remains exact after applying `Hom(-, Q)` for any projective
coefficient module `Q`. Consequently every map from its cycles to `Q` extends to the containing
term. These extensions are the input for lifting maps between complete resolutions and for
identifying finite projectives as relative injectives among Gorenstein-projective modules.

The dual exactness in `CochainComplex.IsTotallyAcyclic` tests only the regular module. A
projective module `Q` is a retract of a free module `Q →₀ A`, and since the terms of the complex
are finitely generated, a map from a term to `Q →₀ A` lands in the functions supported on a finite
set (`LinearMap.exists_finset_support_subset`), a finite power of the regular module. No
self-injectivity or commutativity assumption is needed. Taking the coefficient ring to be `Rᵐᵒᵖ`
gives the statements for right `R`-modules.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 4.
* Edgar E. Enochs and Overtoun M. G. Jenda, *Relative Homological Algebra*, Section 10.2.

The free retraction is Mathlib's `Module.projective_def'`.
-/

public section

open CategoryTheory Limits

universe u v w

namespace CochainComplex.IsTotallyAcyclic

variable {A : Type u} [Ring A] {P : CochainComplex (ModuleCat.{v} A) ℤ}
  (hP : P.IsTotallyAcyclic)
  {Q : Type w} [AddCommGroup Q] [Module A Q] [Module.Projective A Q]

include hP

/-- Applying `Hom(-, Q)` to a totally acyclic complex is exact for every projective coefficient
module `Q`, even over a noncommutative ring. -/
theorem exact_hom_projective (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    Function.Exact (fun f : P.X k →ₗ[A] Q => f.comp (P.d j k).hom)
      (fun f : P.X j →ₗ[A] Q => f.comp (P.d i j).hom) := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective A Q›
  have := hP.finite j
  intro f
  constructor
  · intro hf
    -- As `Pʲ` is finitely generated, `s ∘ f` takes values in functions supported on a finite `T`.
    obtain ⟨T, hT⟩ := (s ∘ₗ f).exists_finset_support_subset
    -- Extend each coordinate in `T` along the differential, then map back to the retract `Q`.
    have hcoord (t : Q) : ∃ g : P.X k →ₗ[A] A,
        g.comp (P.d j k).hom = (Finsupp.lapply t).comp (s.comp f) := by
      apply (hP.exact_dual i j k hij hjk _).mp
      ext y
      have hy := LinearMap.congr_fun hf y
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hy
      simp [hy]
    choose g hg using hcoord
    refine ⟨Finsupp.linearCombination A id ∘ₗ ∑ t ∈ T, Finsupp.lsingle t ∘ₗ g t, ?_⟩
    have heq : (∑ t ∈ T, Finsupp.lsingle t ∘ₗ g t) ∘ₗ (P.d j k).hom = s ∘ₗ f := by
      ext y : 1
      have hsum := Finsupp.sum_of_support_subset (s (f y)) (hT y) Finsupp.single (by simp)
      rw [Finsupp.sum_single] at hsum
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hsum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      have := LinearMap.congr_fun (hg t) y
      simp only [LinearMap.comp_apply, Finsupp.lapply_apply] at this
      simp [this]
    dsimp only
    rw [LinearMap.comp_assoc, heq, ← LinearMap.comp_assoc, hs, LinearMap.id_comp]
  · rintro ⟨g, rfl⟩
    ext x
    have hz := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (P.d_comp_d i j k)) x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at hz
    simp [hz]

/-- Every map from the cycles of a totally acyclic complex to a projective module extends to the
containing term, with independent term and coefficient universes. -/
theorem exists_extend_iCycles (n : ℤ) (f : P.cycles n →ₗ[A] Q) :
    ∃ g : P.X n →ₗ[A] Q, g.comp (P.iCycles n).hom = f := by
  let m := (ComplexShape.up ℤ).prev n
  have ht : P.toCycles m n = (P.sc n).toCycles := by
    apply (cancel_mono (P.iCycles n)).mp
    rw [P.toCycles_i]
    exact (P.sc n).toCycles_i.symm
  have hepi : Epi (P.toCycles m n) := by
    rw [ht]
    exact (hP.acyclic n).epi_toCycles
  have hz : (f.comp (P.toCycles m n).hom).comp (P.d (m - 1) m).hom = 0 := by
    rw [LinearMap.comp_assoc, ← ModuleCat.hom_comp]
    simp
  obtain ⟨g, hg⟩ := (hP.exact_hom_projective (m - 1) m n (by simp) (by simp [m])
    (f.comp (P.toCycles m n).hom)).mp hz
  refine ⟨g, ?_⟩
  apply (LinearMap.cancel_right (g := (P.toCycles m n).hom)
    ((ModuleCat.epi_iff_surjective _).mp hepi)).mp
  rw [LinearMap.comp_assoc, ← ModuleCat.hom_comp, P.toCycles_i]
  exact hg

/-- Two maps to a projective module have the same restriction to cycles exactly when
their difference factors through the next differential. Thus cycle extensions are unique
modulo coboundaries in the coefficient Hom complex. -/
theorem comp_iCycles_eq_iff (n : ℤ) (f g : P.X n →ₗ[A] Q) :
    f.comp (P.iCycles n).hom = g.comp (P.iCycles n).hom ↔
      ∃ h : P.X (n + 1) →ₗ[A] Q, h.comp (P.d n (n + 1)).hom = f - g := by
  constructor
  · intro hfg
    let m := (ComplexShape.up ℤ).prev n
    have hz : (f - g).comp (P.d m n).hom = 0 := by
      rw [← P.toCycles_i m n, ModuleCat.hom_comp, ← LinearMap.comp_assoc,
        LinearMap.sub_comp, hfg, sub_self, LinearMap.zero_comp]
    obtain ⟨h, hh⟩ := (hP.exact_hom_projective m n (n + 1) (by simp [m]) rfl
      (f - g)).mp hz
    exact ⟨h, hh⟩
  · rintro ⟨h, hh⟩
    rw [← sub_eq_zero, ← LinearMap.sub_comp, ← hh, LinearMap.comp_assoc,
      ← ModuleCat.hom_comp, P.iCycles_d, ModuleCat.hom_zero, LinearMap.comp_zero]

end CochainComplex.IsTotallyAcyclic
