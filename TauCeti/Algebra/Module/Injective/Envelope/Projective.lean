/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.Algebra.Module.Injective.Envelope.Basic
public import TauCeti.LinearAlgebra.Finsupp.Supported

/-!
# Projective injective envelopes of finitely generated modules

If an injective envelope `f : M → Q` of a finitely generated module is projective, then `Q` is
finitely generated (`TauCeti.IsInjectiveEnvelope.finite_of_projective`), over any ring. Indeed `Q`
is a direct summand of a free module, through a section `s : Q → R^(Q)` of the linear combination
map; the image of `M` lies in finitely many coordinates `T`, so the projection `Q → R^T` is
injective on `M`, hence injective on `Q` by essentiality, and it splits because `Q` is injective.

This is what makes a projective-injective coresolution of a finitely generated module by injective
envelopes consist of finitely generated modules.

## Main results

* `TauCeti.IsInjectiveEnvelope.finite_of_projective`: a projective injective envelope of a finitely
  generated module is finitely generated.
-/

public section

universe w

namespace TauCeti

variable {R : Type*} [Ring R] {M : Type*} {Q : Type w} [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q]

/-- **A projective injective envelope of a finitely generated module is finitely generated.** -/
theorem IsInjectiveEnvelope.finite_of_projective [Small.{w} R] [Module.Finite R M]
    [Module.Projective R Q] {f : M →ₗ[R] Q} (hf : IsInjectiveEnvelope f) : Module.Finite R Q := by
  have := hf.moduleInjective
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective R Q›
  -- The finitely many coordinates `T` used by the image of `M`.
  obtain ⟨T, hT⟩ := (s ∘ₗ f).exists_finset_support_subset
  let p : Q →ₗ[R] (T → R) := LinearMap.pi fun t ↦ Finsupp.lapply t.val ∘ₗ s
  have hpf : Function.Injective (p ∘ₗ f) := by
    refine (injective_iff_map_eq_zero _).2 fun m hm ↦ hf.injective ?_
    have hzero : s (f m) = 0 := by
      ext a
      by_cases ha : a ∈ T
      · exact congrFun hm ⟨a, ha⟩
      · exact Finsupp.notMem_support_iff.1 fun h ↦ ha (hT m h)
    rw [map_zero, ← LinearMap.id_apply (R := R) (f m), ← hs, LinearMap.comp_apply, hzero,
      map_zero]
  have hp : Function.Injective p := hf.isEssential_range.injective_of_injective_comp hpf
  obtain ⟨h, hhp⟩ := Module.Injective.extension_property R Q Q (T → R) p hp LinearMap.id
  exact Module.Finite.of_surjective h fun q ↦ ⟨p q, by simpa using congrArg (· q) hhp⟩

end TauCeti
