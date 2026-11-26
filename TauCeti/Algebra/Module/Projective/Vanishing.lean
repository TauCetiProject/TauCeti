/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Ideal.Prime

/-!
# Vanishing of elements of projective modules

An element `s` of a projective `A`-module vanishes if for every nonzero `a : A` there is a prime
`p` avoiding `a` such that `s` vanishes in the localization at `p`
(`Module.Projective.eq_zero_of_forall_ne_zero`). Indeed, a projective module is a direct summand
of a free module, and each coordinate `a` of `s` in that free module is killed by an element
outside every such prime; if `a` were nonzero, choosing the prime to avoid `a` would contradict
primality.
-/

public section

/-- An element `s` of a projective `A`-module vanishes if for every nonzero `a : A` there is a
prime `p` with `a ∉ p` such that `s` is killed by some element outside `p`, that is, `s` vanishes
in the localization at `p`. -/
theorem Module.Projective.eq_zero_of_forall_ne_zero {A P : Type*} [CommRing A] [AddCommGroup P]
    [Module A P] [Module.Projective A P] {s : P}
    (h : ∀ a : A, a ≠ 0 → ∃ p : Ideal A, p.IsPrime ∧ a ∉ p ∧ ∃ u ∉ p, u • s = 0) : s = 0 := by
  obtain ⟨f, hf⟩ := Module.projective_def'.mp ‹_›
  suffices hs : f s = 0 by simpa [hs] using (LinearMap.congr_fun hf s).symm
  ext i
  by_contra hi
  obtain ⟨p, hp, hap, u, hu, hus⟩ := h _ hi
  have hui : u * f s i = 0 := by simpa using congr(f $hus i)
  exact (hp.mem_or_mem (hui ▸ p.zero_mem)).elim hu hap
