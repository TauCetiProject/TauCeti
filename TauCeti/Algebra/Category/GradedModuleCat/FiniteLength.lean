/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Abelian
public import TauCeti.CategoryTheory.Simple.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# Simple quotients of finite graded modules

A nonzero graded module finite-dimensional over its scalar field admits a graded surjection
onto a simple object. No finite-dimensionality or positivity assumption on the algebra is
needed. These quotients detect nonzero finite graded modules, in particular the degree
quotients of terms of minimal resolutions.

## References

* `TauCeti.span_range_laurentK0_of_eq_top`, for the graded simple-class spanning argument.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
-/

public section

namespace TauCeti.GradedModuleCat

open CategoryTheory CategoryTheory.Limits

universe uk uA v

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-- A nonzero finite-dimensional graded module which is not simple has a proper subobject
and a nonzero cokernel, both finite-dimensional and of strictly smaller dimension. -/
theorem exists_mono_cokernel_finrank_lt (M : GradedModuleCat.{v} 𝒜) [Module.Finite k M]
    (hM : ¬IsZero M) (hs : ¬Simple M) :
    ∃ (Y : GradedModuleCat.{v} 𝒜) (i : Y ⟶ M),
      Mono i ∧ Module.Finite k Y ∧ Module.Finite k (cokernelObj i) ∧
        ¬IsZero (cokernelObj i) ∧ Module.finrank k Y < Module.finrank k M ∧
          Module.finrank k (cokernelObj i) < Module.finrank k M := by
  classical
  obtain ⟨Y, i, hi, hi₀, hiiso⟩ := exists_mono_ne_zero_not_isIso_of_not_simple hM hs
  have : Mono i := hi
  have hinj := (mono_iff_injective i).mp hi
  let Q := cokernelObj i
  have : Module.Finite k Y := FiniteDimensional.of_injective (i.hom.restrictScalars k) hinj
  have hπ : Function.Surjective (cokernelπ i).hom := Submodule.mkQ_surjective _
  have : Module.Finite k Q := Module.Finite.of_surjective
    ((cokernelπ i).hom.restrictScalars k) hπ
  have hQ : ¬IsZero Q := by
    intro hQ
    have : Epi i := Preadditive.epi_of_isZero_cokernel' (cokernelCocone i) (cokernelIsColimit i) hQ
    exact hiiso (isIso_of_mono_of_epi i)
  have : Nontrivial Y := by
    by_contra hY
    rw [not_nontrivial_iff_subsingleton] at hY
    exact hi₀ (hom_ext (LinearMap.ext fun x ↦ by
      rw [Subsingleton.elim x 0, map_zero, map_zero]))
  have : Nontrivial Q := by
    by_contra hzero
    rw [not_nontrivial_iff_subsingleton] at hzero
    exact hQ ((IsZero.iff_id_eq_zero Q).mpr
      (hom_ext (LinearMap.ext fun _ ↦ Subsingleton.elim _ _)))
  have hdim : Module.finrank k Q = Module.finrank k M - Module.finrank k Y := by
    rw [Submodule.finrank_quotient (R := k),
      ← LinearEquiv.finrank_eq ((LinearEquiv.ofInjective i.hom hinj).restrictScalars k)]
  have hYpos := Module.finrank_pos (R := k) (M := Y)
  have hQpos := Module.finrank_pos (R := k) (M := Q)
  have hYdim : Module.finrank k Y < Module.finrank k M := by omega
  have hQdim : Module.finrank k Q < Module.finrank k M := by omega
  exact ⟨Y, i, hi, inferInstance, inferInstance, hQ, hYdim, hQdim⟩

/-- Every nonzero finite-dimensional graded module has a simple graded quotient. The quotient
is finite-dimensional over the same field and lies in the same universe as the source. -/
theorem exists_simple_quotient (M : GradedModuleCat.{v} 𝒜) [Module.Finite k M]
    (hM : ¬IsZero M) :
    ∃ (N : GradedModuleCat.{v} 𝒜) (f : M ⟶ N),
      Module.Finite k N ∧ Simple N ∧ Epi f := by
  classical
  induction hn : Module.finrank k M using Nat.strong_induction_on generalizing M with
  | _ n ih =>
    by_cases hs : Simple M
    · exact ⟨M, 𝟙 M, inferInstance, hs, inferInstance⟩
    obtain ⟨Y, i, hi, hYfinite, hQfinite, hQ, _, hdim⟩ :=
      M.exists_mono_cokernel_finrank_lt hM hs
    have : Module.Finite k (cokernelObj i) := hQfinite
    obtain ⟨N, f, hN, hsN, hf⟩ := ih _ (hn ▸ hdim) (cokernelObj i) hQ rfl
    have : Epi f := hf
    have : Epi (cokernelπ i) := (epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
    exact ⟨N, cokernelπ i ≫ f, hN, hsN, inferInstance⟩

end TauCeti.GradedModuleCat
