/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
import Mathlib.Dynamics.Newton

/-!
# Henselian pairs and radicals

If `(R, I)` is a henselian pair, then so is `(R, √I)`. This permits the universal property of
henselization to be applied to maps carrying an ideal into the radical of the target ideal.
No finite generation or Noetherian hypothesis is needed.

The proof uses Mathlib's `Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero`
(Antoine Chambert-Loir and Oliver Nash): a simple root modulo `√I` first lifts to a root
modulo `I` by Newton iteration, and then lifts to `R` by henselianity.

## References

* [Stacks Project, Lemma 15.11.7](https://stacks.math.columbia.edu/tag/09XJ).
-/

public section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- Taking the radical of the ideal of a henselian pair preserves henselianity. -/
instance henselianRing_radical (I : Ideal R) [HenselianRing R I] : HenselianRing R I.radical where
  jac := (isRadical_jacobson ⊥).radical_le_iff.2 HenselianRing.jac
  is_henselian f hf a₀ ha hu := by
    have hjac : I.radical ≤ jacobson ⊥ :=
      (isRadical_jacobson ⊥).radical_le_iff.2 HenselianRing.jac
    have := isLocalHom_of_le_jacobson_bot I.radical hjac
    have hunit : IsUnit (f.derivative.eval a₀) := isUnit_of_map_unit _ _ hu
    have hnil : IsNilpotent (Polynomial.aeval (Quotient.mk I a₀) f) := by
      obtain ⟨n, hn⟩ := ha
      refine ⟨n, ?_⟩
      simpa [Polynomial.aeval_def, Polynomial.eval₂_at_apply, ← map_pow] using
        (Quotient.eq_zero_iff_mem.2 hn)
    have hderiv : IsUnit (Polynomial.aeval (Quotient.mk I a₀) f.derivative) := by
      simpa [Polynomial.aeval_def, Polynomial.eval₂_at_apply] using
        hunit.map (Quotient.mk I)
    obtain ⟨b, ⟨hb, hfb⟩, -⟩ :=
      f.existsUnique_nilpotent_sub_and_aeval_eq_zero hnil hderiv
    obtain ⟨b, rfl⟩ := Quotient.mk_surjective b
    have hfb' : f.eval b ∈ I := by
      apply Quotient.eq_zero_iff_mem.1
      simpa [Polynomial.aeval_def, Polynomial.eval₂_at_apply] using hfb
    have hba : b - a₀ ∈ I.radical := by
      obtain ⟨n, hn⟩ := hb.neg
      refine ⟨n, Quotient.eq_zero_iff_mem.1 ?_⟩
      simpa [map_sub, map_pow, neg_sub] using hn
    have hunitb : IsUnit (Quotient.mk I (f.derivative.eval b)) := by
      simpa [Polynomial.aeval_def, Polynomial.eval₂_at_apply] using
        Polynomial.isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub
          (a := Quotient.mk I b) hderiv (by simpa [neg_sub] using hb.neg)
    obtain ⟨a, hfa, hab⟩ := HenselianRing.is_henselian f hf b hfb' hunitb
    exact ⟨a, hfa, by simpa using I.radical.add_mem (le_radical hab) hba⟩

end Ideal
