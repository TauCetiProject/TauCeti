/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotallyAcyclic.Basic
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# Projective coefficients for complete resolutions

A totally acyclic complex remains exact after applying `Hom(-, Q)` for any finitely generated
projective coefficient module `Q`. Consequently every map from its cycles to `Q` extends to the
containing term. These extensions are the input for lifting maps between complete resolutions and
for identifying finite projectives as relative injectives among Gorenstein-projective modules.

The dual exactness in `CochainComplex.IsTotallyAcyclic` tests only the regular module. Finite
projective coefficients are retracts of finite powers of that module; no self-injectivity or
commutativity assumption is needed. Taking the coefficient ring to be `Rᵐᵒᵖ` gives the statements
for right `R`-modules.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 4.
* Edgar E. Enochs and Overtoun M. G. Jenda, *Relative Homological Algebra*, Section 10.2.

The finite-free retraction is Mathlib's `Module.Finite.exists_comp_eq_id_of_projective`.
-/

public section

open CategoryTheory Limits

universe u v w

namespace CochainComplex.IsTotallyAcyclic

variable {A : Type u} [Ring A] {P : CochainComplex (ModuleCat.{v} A) ℤ}
  (hP : P.IsTotallyAcyclic)
  {Q : Type w} [AddCommGroup Q] [Module A Q] [Module.Finite A Q] [Module.Projective A Q]

include hP

/-- Applying `Hom(-, Q)` to a totally acyclic complex is exact for every finitely generated
projective coefficient module `Q`, even over a noncommutative ring. -/
theorem exact_hom_projective (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    Function.Exact (fun f : P.X k →ₗ[A] Q => f.comp (P.d j k).hom)
      (fun f : P.X j →ₗ[A] Q => f.comp (P.d i j).hom) := by
  classical
  obtain ⟨n, r, s, -, -, hrs⟩ := Module.Finite.exists_comp_eq_id_of_projective A Q
  intro f
  constructor
  · intro hf
    -- Extend each coordinate in a finite free module, then project back to its retract `Q`.
    have hcoord (a : Fin n) :
        ∃ g : P.X k →ₗ[A] A,
          g.comp (P.d j k).hom = (LinearMap.proj a).comp (s.comp f) := by
      apply (hP.exact_dual i j k hij hjk _).mp
      ext x
      have hx := LinearMap.congr_fun hf x
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hx
      simp [hx]
    choose g hg using hcoord
    refine ⟨r.comp (LinearMap.pi g), ?_⟩
    have heq : (LinearMap.pi g).comp (P.d j k).hom = s.comp f := by
      ext x a
      exact LinearMap.congr_fun (hg a) x
    dsimp only
    rw [LinearMap.comp_assoc, heq, ← LinearMap.comp_assoc, hrs, LinearMap.id_comp]
  · rintro ⟨g, rfl⟩
    ext x
    have hz := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (P.d_comp_d i j k)) x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at hz
    simp [hz]

/-- Every map from the cycles of a totally acyclic complex to a finite projective module
extends to the containing term, with independent term and coefficient universes. -/
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

/-- Two maps to a finite projective module have the same restriction to cycles exactly when
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
