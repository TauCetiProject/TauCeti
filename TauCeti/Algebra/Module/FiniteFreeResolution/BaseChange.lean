/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Algebra.Module.FiniteFreeResolution.Basic
import TauCeti.LinearAlgebra.Exact

/-!
# Flat base change of finite free resolutions

If `A` is a flat `R`-algebra, tensoring a finite free resolution `0 → Fₙ → ⋯ → F₀ → M → 0` with
`A` gives a finite free resolution of `A ⊗[R] M` over `A` of the same length: the terms
`A ⊗[R] Fᵢ` are finite free over `A`, and flatness keeps the sequence exact. This is how finite
free resolutions are moved from a ring to its localizations and to polynomial rings over it.

## Main results

* `TauCeti.Module.HasFiniteFreeResolutionLE.baseChange`: flat base change of a finite free
  resolution of length at most `n`.
* `TauCeti.Module.HasFiniteFreeResolution.baseChange`: flat base change of a finite free
  resolution.

## References

* S. Lang, *Algebra*, third edition, Graduate Texts in Mathematics 211, Springer (2002),
  Chapter XXI, §2.
-/

public section

namespace TauCeti.Module

open LinearMap TensorProduct

universe u

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
  (A : Type u) [Ring A] [Algebra R A] [Module.Flat R A]

/-- **Flat base change.** If `A` is a flat `R`-algebra and `M` has a finite free resolution of
length at most `n` over `R`, then `A ⊗[R] M` has one of length at most `n` over `A`. -/
theorem HasFiniteFreeResolutionLE.baseChange {n : ℕ}
    (h : HasFiniteFreeResolutionLE R n M) : HasFiniteFreeResolutionLE A n (A ⊗[R] M) := by
  induction n generalizing M with
  | zero =>
    obtain ⟨_, _⟩ := hasFiniteFreeResolutionLE_zero_iff.mp h
    exact hasFiniteFreeResolutionLE_zero
  | succ n ih =>
    obtain ⟨k, f, hf, hK⟩ := hasFiniteFreeResolutionLE_succ_iff.mp h
    -- Tensoring `0 → ker f → Rᵏ → M → 0` with the flat module `A` keeps it exact, so the kernel
    -- of `A ⊗ f` is `A ⊗ ker f`.
    have hexact : Function.Exact ((ker f).subtype.baseChange A) (f.baseChange A) := by
      rw [baseChange_eq_lTensor, baseChange_eq_lTensor]
      exact lTensor_exact A f.exact_subtype_ker_map hf
    have hinj : Function.Injective ((ker f).subtype.baseChange A) := by
      rw [baseChange_eq_lTensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ (ker f).injective_subtype
    have hsurj : Function.Surjective (f.baseChange A) := by
      rw [baseChange_eq_lTensor]
      exact lTensor_surjective A hf
    exact succ_of_surjective hsurj ((ih hK).of_equiv (hexact.linearEquivOfInjective hinj))

/-- **Flat base change.** If `A` is a flat `R`-algebra and `M` has a finite free resolution over
`R`, then `A ⊗[R] M` has one over `A`. -/
theorem HasFiniteFreeResolution.baseChange (h : HasFiniteFreeResolution R M) :
    HasFiniteFreeResolution A (A ⊗[R] M) :=
  let ⟨n, h⟩ := hasFiniteFreeResolution_iff.mp h
  hasFiniteFreeResolution_iff.mpr ⟨n, h.baseChange A⟩

end TauCeti.Module
