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
dimension or a bound on the lengths of the resolutions.

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
