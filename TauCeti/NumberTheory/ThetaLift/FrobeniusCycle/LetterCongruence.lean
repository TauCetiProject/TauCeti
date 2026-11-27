/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Frobenius.Localization

/-!
# Frobenius congruence for conjugation-corrected letters

In a signed Frobenius orbit, the ordinary Frobenius step is followed by an involution. To
read two letters at the same local prime, precompose the letter at the conjugate prime by
that involution. The corrected maps then differ by an ordinary local Frobenius power. In
particular, at an unramified prime the congruence holds modulo the rational prime, not just
modulo the maximal ideal of the target.

## References

* The signed step and correction in `New.Data.dvd_letterEmbedding_sub_pow` in
  `grh/src/New/UpperBound/Divisibility/MarkOperator.lean` of lsernau/grh-lean at `72fead1`.
-/

public section

namespace TauCeti.FrobeniusCycle

/-- Suppose consecutive raw letters on the original ring are `u` and `u ∘ φ^e ∘ c`, where
`c` is an involution commuting with the arithmetic Frobenius `φ`. If their corrected maps `f`
and `g` on the localization use opposite conjugation choices, then `g(y)` is congruent to
`f(y)^(p^e)` modulo `p` for every local element `y`. The raw letters need not themselves extend
to the same localization. -/
theorem dvd_letterEmbedding_sub_pow {S R : Type*} [CommRing S] [CommRing R]
    [Algebra.EssFiniteType ℤ S] {Q : Ideal S} [Q.IsPrime] [Algebra.IsUnramifiedAt ℤ Q]
    {p e : ℕ} [Q.LiesOver (Ideal.span {(p : ℤ)})] {φ : S →ₐ[ℤ] S} (hφ : φ.IsArithFrobAt Q)
    {c : S →ₐ[ℤ] S} (hc : c * c = 1) (hcomm : Commute c (φ ^ e))
    (u : S →+* R) (f g : Localization.AtPrime Q →+* R) (b : Bool)
    (hf : ∀ x, f (algebraMap S (Localization.AtPrime Q) x) = u (if b then c x else x))
    (hg : ∀ x, g (algebraMap S (Localization.AtPrime Q) x) =
      u ((φ ^ e) (c (if b then x else c x)))) (y : Localization.AtPrime Q) :
    (p : R) ∣ g y - f y ^ p ^ e := by
  have hinvol (x : S) : c (c x) = x := congrArg (fun k : S →ₐ[ℤ] S ↦ k x) hc
  have hmove (x : S) : c ((φ ^ e) x) = (φ ^ e) (c x) :=
    congrArg (fun k : S →ₐ[ℤ] S ↦ k x) hcomm.eq
  have hlocal : g = f.comp ↑(hφ.localize ^ e) := by
    apply IsLocalization.ringHom_ext Q.primeCompl
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, hφ.localize_pow_algebraMap, hf, hg]
    cases b
    · simp only [Bool.false_eq_true, ite_false, hinvol]
    · simp only [ite_true, hmove]
  rw [hlocal, RingHom.comp_apply, AlgHom.coe_toRingHom]
  exact hφ.natCast_dvd_localize_pow_sub_pow f e y

end TauCeti.FrobeniusCycle
