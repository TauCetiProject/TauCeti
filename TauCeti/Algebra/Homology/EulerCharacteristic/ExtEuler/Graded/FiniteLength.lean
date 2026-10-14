/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.FiniteLength
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Shift

/-!
# Graded Euler-admissibility from simple sources

For a fixed target, graded Euler-admissibility of finite-dimensional sources can be tested on
simple graded modules. Both internal finiteness and eventual cohomological vanishing propagate
through graded composition series. The algebra need not itself be finite-dimensional.

Together with the source-shift admissibility results in
`TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Shift`, this criterion lets an
exhaustive family of simples up to shift supply the finiteness data for a q-Euler form.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.4--2.7.

The dimension induction uses `GradedModuleCat.exists_mono_cokernel_finrank_lt`;
the extension step uses `IsGradedEulerAdmissible.of_shortExact₂'`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe w uk uA v

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [HasExt.{w} (GradedModuleCat.{v} 𝒜)]

/-- Admissibility against every finite-dimensional simple source implies admissibility against
all finite-dimensional graded sources, for any chosen internal-shift autoequivalence. -/
theorem isGradedEulerAdmissible_of_finite_of_forall_simple
    (e : GradedModuleCat.{v} 𝒜 ≌ GradedModuleCat.{v} 𝒜) (Y : GradedModuleCat.{v} 𝒜)
    (h : ∀ S : GradedModuleCat.{v} 𝒜, Module.Finite k S → Simple S →
      IsGradedEulerAdmissible.{w} k e S Y)
    (X : GradedModuleCat.{v} 𝒜) [Module.Finite k X] :
    IsGradedEulerAdmissible.{w} k e X Y := by
  classical
  induction hn : Module.finrank k X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    by_cases hX : IsZero X
    · have : Projective X := hX.projective
      have hsub (j : ℤ) : Subsingleton (X ⟶ (e ^ j).functor.obj Y) :=
        ⟨fun f g ↦ hX.eq_of_src f g⟩
      exact isGradedEulerAdmissible_of_projective k e X Y
        (HasFiniteLaurentSupport.of_finset (fun _ ↦ inferInstance) ∅ fun j _ ↦ hsub j)
    by_cases hs : Simple X
    · exact h X inferInstance hs
    obtain ⟨Z, i, hi, hZ, hQ, _, hdimZ, hdimQ⟩ :=
      X.exists_mono_cokernel_finrank_lt hX hs
    have : Module.Finite k Z := hZ
    have : Module.Finite k (GradedModuleCat.cokernelObj i) := hQ
    let S := ShortComplex.mk i (GradedModuleCat.cokernelπ i) (by simp)
    have hS : S.ShortExact :=
      { exact := GradedModuleCat.exact_iff.mpr (LinearMap.exact_map_mkQ_range i.hom)
        mono_f := hi
        epi_g := (GradedModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _) }
    exact (ih _ (hn ▸ hdimZ) Z rfl).of_shortExact₂' hS
      (ih _ (hn ▸ hdimQ) (GradedModuleCat.cokernelObj i) rfl)

end TauCeti
