/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Projective.MinimalResolution.Uniqueness
public import TauCeti.Algebra.Homology.Periodic.Resolution

/-!
# Homotopy invariance of minimal periodic tails

For minimal complexes of finite modules over a commutative ring, a homotopy equivalence
preserves a periodic tail with exactly the same period and preperiod. In particular,
eventual periodicity is independent of the chosen minimal projective resolution.

Minimality is essential: adjoining contractible disks can change the terms in arbitrarily
high degrees without changing the homotopy type. We do not assert that strict periodicity
of an arbitrary projective resolution is a homotopy invariant. The result applies to local
rings, where minimality is the maximal-ideal criterion, without requiring finite projective
dimension or a bound on the lengths of the resolutions. Unfolding a periodic complex of modules
preserves and reflects minimality (`TauCeti.PeriodicComplex.resolutionComplex_isMinimal_iff`).

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5 and Theorem 6.1.
-/

public section

open CategoryTheory

universe u v

namespace HomotopyEquiv

variable {R : Type u} [CommRing R] {K L : ChainComplex (ModuleCat.{v} R) ℕ}
  [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Finite R (L.X i)]

/-- A homotopy equivalence between minimal complexes of finite modules preserves periodic
tails, including their period and preperiod. -/
theorem hasPeriodicTail_iff_of_isMinimal (e : HomotopyEquiv K L)
    (hK : K.IsMinimal) (hL : L.IsMinimal) (n p : ℕ) :
    K.HasPeriodicTail n p ↔ L.HasPeriodicTail n p := by
  have := hK.isIso_hom_of_homotopyEquiv hL e
  exact ⟨fun h ↦ h.of_iso (asIso e.hom), fun h ↦ h.of_iso (asIso e.hom).symm⟩

end HomotopyEquiv

namespace CategoryTheory.ProjectiveResolution

variable {R : Type u} [CommRing R] {M : ModuleCat.{v} R}
  (P Q : ProjectiveResolution M)
  [∀ i, Module.Finite R (P.complex.X i)] [∀ i, Module.Finite R (Q.complex.X i)]

/-- Periodicity with a specified preperiod is independent of the chosen minimal projective
resolution with finite terms. -/
theorem hasPeriodicTail_iff_of_isMinimal
    (hP : P.complex.IsMinimal) (hQ : Q.complex.IsMinimal) (n p : ℕ) :
    P.complex.HasPeriodicTail n p ↔ Q.complex.HasPeriodicTail n p :=
  (P.homotopyEquiv Q).hasPeriodicTail_iff_of_isMinimal hP hQ n p

end CategoryTheory.ProjectiveResolution

namespace TauCeti.PeriodicComplex

private theorem zmod_sub_natCast_add_one {n : ℕ} (j : ℤ) (k : ℕ) :
    ((j - (k + 1 : ℕ) : ℤ) : ZMod n) + 1 = ((j - k : ℤ) : ZMod n) := by
  push_cast
  ring

/-- Unfolding a positive-period `ZMod n`-indexed complex of modules from any starting index `j : ℤ`
gives a minimal chain complex if and only if the periodic complex is minimal. -/
theorem resolutionComplex_isMinimal_iff {R : Type u} [CommRing R] {n : ℕ} [NeZero n]
    (Q : HomologicalComplex (ModuleCat.{v} R) (ComplexShape.up (ZMod n))) (j : ℤ) :
    (resolutionComplex Q j).IsMinimal ↔ Q.IsMinimal := by
  rw [ChainComplex.isMinimal_iff_range_d_succ_le, HomologicalComplex.isMinimal_iff_forall_rel]
  refine ⟨fun h a b hab ↦ ?_, fun h k ↦ ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, ((j - k : ℤ) : ZMod n) = b :=
      ⟨((j : ZMod n) - b).val, by push_cast; simp⟩
    have hk' : ((j - (k + 1 : ℕ) : ℤ) : ZMod n) = a :=
      add_right_cancel ((zmod_sub_natCast_add_one j k).trans (hk.trans hab.symm))
    subst hk hk'
    rintro _ ⟨x, rfl⟩
    exact resolutionComplex_d Q j k ▸ h k ⟨x, rfl⟩
  · rw [resolutionComplex_d]
    exact h _ _ (zmod_sub_natCast_add_one j k)

end TauCeti.PeriodicComplex
