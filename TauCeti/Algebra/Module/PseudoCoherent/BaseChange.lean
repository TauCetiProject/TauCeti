/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.PseudoCoherent.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic

/-!
# Flat base change of pseudocoherent modules

Extension of scalars along a flat algebra preserves pseudocoherence, in every finite degree
and in degree infinity. This supplies the module-theoretic stability needed for flat pullback
of locally pseudocoherent sheaves. No Noetherian or finite-presentation hypothesis is imposed
on the algebra.

The proof tensors the finite free resolution defining `TauCeti.Huber.IsPseudoCoherentOver`.
It uses Mathlib's `Module.Flat.lTensor_exact` for exactness and
`TensorProduct.piScalarRight` to put the resulting free modules in coordinate form.

## References

* The Stacks Project, Lemma 15.66.13, Tag 066C (flat base change).
-/

public section

namespace TauCeti.Huber.IsPseudoCoherentOver

open LinearMap TensorProduct

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {m : ℕ∞}

/-- Flat extension of scalars preserves `m`-pseudocoherence, including `m = ⊤`. -/
theorem baseChange (h : IsPseudoCoherentOver R M m) (S : Type*) [CommRing S] [Algebra R S]
    [Module.Flat R S] : IsPseudoCoherentOver S (S ⊗[R] M) m := by
  classical
  rw [isPseudoCoherentOver_iff] at h ⊢
  obtain ⟨n, d, ε, hε, h₀, hd⟩ := h
  let e (i : ℕ) := TensorProduct.piScalarRight R S S (Fin (n i))
  refine ⟨n, fun i ↦ (e i).toLinearMap ∘ₗ (d i).baseChange S ∘ₗ (e (i + 1)).symm,
    ε.baseChange S ∘ₗ (e 0).symm,
    (ε.baseChange_surjective S hε).comp (e 0).symm.surjective, ?_, ?_⟩
  · intro hm
    dsimp only
    rw [← LinearMap.comp_assoc, LinearEquiv.precomp_exact_iff_exact,
      LinearEquiv.conj_exact_iff_exact]
    simpa only [LinearMap.baseChange_eq_lTensor] using Module.Flat.lTensor_exact S (h₀ hm)
  · intro i hi
    dsimp only
    rw [← LinearMap.comp_assoc, LinearEquiv.precomp_exact_iff_exact,
      LinearEquiv.postcomp_exact_iff_exact, LinearEquiv.conj_exact_iff_exact]
    simpa only [LinearMap.baseChange_eq_lTensor] using Module.Flat.lTensor_exact S (hd i hi)

end TauCeti.Huber.IsPseudoCoherentOver
