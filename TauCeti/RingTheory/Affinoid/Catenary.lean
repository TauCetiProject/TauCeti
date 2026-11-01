/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Basic
public import TauCeti.RingTheory.RegularLocalRing.Catenary
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Regular

/-!
# Affinoid algebras are universally catenary

An affinoid algebra over a complete nonarchimedean field is universally catenary: every algebra
of finite type over it is catenary. This includes nonreduced algebras and the zero algebra,
and requires neither a nontrivial valuation nor a chosen topology on the affinoid algebra.

A Tate algebra is regular, hence universally catenary. Universal catenarity passes to its
surjective images, so any Tate presentation gives the result. This is the catenarity input
to excellence of affinoid algebras; it does not assert the remaining excellence conditions.

## References

* B. Conrad, *Irreducible components of rigid spaces*, Ann. Inst. Fourier 49 (1999),
  §1.1, for the algebraic properties of affinoid algebras used in excellence.
* Stacks Project, Lemmas 10.105.7 (Tag 00NK) and 10.105.9 (Tag 00NM), for quotient
  permanence and universal catenarity of regular rings.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A]

/-- **Affinoid algebras are universally catenary.** Every algebra of finite type over an affinoid
algebra over a complete nonarchimedean field is catenary. No reducedness or nontriviality
hypothesis is required. -/
theorem isUniversallyCatenary (hA : IsAffinoidAlgebra K A) :
    Excellence.IsUniversallyCatenary A := by
  obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K A).mp hA
  exact π.toRingHom.isUniversallyCatenary_of_surjective hπ

end TauCeti.IsAffinoidAlgebra
