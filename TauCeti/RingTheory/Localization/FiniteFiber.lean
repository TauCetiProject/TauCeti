/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Localization at a singleton fibre of a finite algebra

For an integral algebra `R → S`, suppose `q` is the only prime over a prime `p` of `R`.
Localizing `S` at the image of `R ∖ p` then already inverts every element outside `q`.
Consequently `S_q` is the base localization of `S`, and if `S` is finite over `R`, then
`S_q` is finite over `R_p`.

This is the algebraic step that turns a finite morphism with a single point over a chosen
base point into a finite homomorphism of local rings. Without the singleton-fibre hypothesis,
a stalk of a finite morphism need not be finite over the corresponding base stalk.

## References

* The Stacks Project, proof of Lemma 58.21.4 (Tag 0BMB), the reduction to a finite local
  homomorphism after elementary étale localization.
-/

public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If an integral algebra has exactly one prime `q` above `p`, localization at `q` is
already localization at the image of the complement of `p`. No finiteness or Noetherian
hypothesis is needed. -/
theorem isLocalization_atPrime_of_unique_liesOver [Algebra.IsIntegral R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (h : ∀ q' : Ideal S, q'.IsPrime → q'.LiesOver p → q' = q)
    (T : Type*) [CommRing T] [Algebra S T] [IsLocalization.AtPrime T q] :
    IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) T := by
  let M := Algebra.algebraMapSubmonoid S p.primeCompl
  have hMq : M ≤ q.primeCompl := by
    rintro _ ⟨r, hr, rfl⟩
    exact fun hrs ↦ hr ((q.over_def p) ▸ hrs)
  have hsingleton : p.primesOver S = {q} := by
    ext q'
    rw [Set.mem_singleton_iff]
    constructor
    · exact fun hq' ↦ h q' hq'.1 hq'.2
    · rintro rfl
      exact ⟨inferInstance, inferInstance⟩
  apply (IsLocalization.iff_of_le_of_exists_dvd M q.primeCompl hMq ?_).mpr inferInstance
  intro s hs
  obtain ⟨r, hr, hsr⟩ := exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hsingleton s hs
  exact ⟨algebraMap R S r, ⟨r, hr, rfl⟩, hsr⟩

/-- At a singleton fibre, localizing a finite algebra gives a finite algebra over the
localized base. The localization models and their compatible algebra structures are arbitrary. -/
theorem finite_localizationAtPrime_of_unique_liesOver [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (h : ∀ q' : Ideal S, q'.IsPrime → q'.LiesOver p → q' = q)
    (A B : Type*) [CommRing A] [CommRing B] [Algebra R A] [IsLocalization.AtPrime A p]
    [Algebra S B] [IsLocalization.AtPrime B q] [Algebra R B] [Algebra A B]
    [IsScalarTower R S B] [IsScalarTower R A B] : Module.Finite A B := by
  have := p.isLocalization_atPrime_of_unique_liesOver q h B
  exact Module.Finite.of_isLocalization R S p.primeCompl

end Ideal
