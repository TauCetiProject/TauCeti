/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.Algebra.Module.Injective.Envelope.Basic

/-!
# Projective injective envelopes of finitely generated modules

If an injective envelope `f : M → Q` of a finitely generated module is projective, then `Q` is
finitely generated (`TauCeti.IsInjectiveEnvelope.finite_of_projective`), over any ring. Indeed `Q`
is a direct summand of a free module, through a section `s : Q → R^(Q)` of the linear combination
map; the image of `M` lies in finitely many coordinates `T`, so the projection `Q → R^T` is
injective on `M`, hence injective on `Q` by essentiality, and it splits because `Q` is injective.

This is what makes a projective-injective coresolution of a finitely generated module by minimal
injective envelopes consist of finitely generated modules.

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
    [Module.Projective R Q]
    {f : M →ₗ[R] Q} (hf : IsInjectiveEnvelope f) : Module.Finite R Q := by
  have := hf.moduleInjective
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective R Q›
  obtain ⟨k, x, hx⟩ := Module.Finite.exists_fin (R := R) (M := M)
  classical
  -- The finitely many coordinates `T` used by the images of the generators of `M`.
  let T : Finset Q := Finset.univ.biUnion fun j ↦ (s (f (x j))).support
  let p : Q →ₗ[R] (T → R) := LinearMap.pi fun t ↦ Finsupp.lapply t.1 ∘ₗ s
  -- Every element of `M` is sent into the coordinates `T`.
  have hT : ∀ m : M, s (f m) ∈ Finsupp.supported R R (T : Set Q) := by
    have : Submodule.span R (Set.range x) ≤
        (Finsupp.supported R R (T : Set Q)).comap (s ∘ₗ f) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      refine (Finsupp.mem_supported R _).2 fun a ha ↦ ?_
      exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, ha⟩
    intro m
    exact this (hx ▸ Submodule.mem_top)
  have hpf : Function.Injective (p ∘ₗ f) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro m hm
    have hzero : s (f m) = 0 := by
      ext a
      by_cases ha : a ∈ T
      · exact congrFun hm ⟨a, ha⟩
      · exact Finsupp.notMem_support_iff.1 fun h ↦ ha ((Finsupp.mem_supported R _).1 (hT m) h)
    apply hf.injective
    rw [map_zero, ← LinearMap.id_apply (R := R) (f m), ← hs, LinearMap.comp_apply, hzero,
      map_zero]
  have hp : Function.Injective p := hf.isEssential_range.injective_of_injective_comp hpf
  obtain ⟨h, hhp⟩ := Module.Injective.extension_property R Q Q (T → R) p hp LinearMap.id
  exact Module.Finite.of_surjective h fun q ↦ ⟨p q, by simpa using congrArg (· q) hhp⟩

end TauCeti
