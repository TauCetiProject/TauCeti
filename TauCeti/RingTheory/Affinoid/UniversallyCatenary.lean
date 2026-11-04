/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Basic
public import TauCeti.RingTheory.UniversallyCatenary
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Regular
import TauCeti.RingTheory.RegularLocalRing.Catenary

/-!
# Affinoid algebras are universally catenary

Every affinoid algebra over a complete nonarchimedean field is universally catenary: it is
noetherian, and every algebra of finite type over it is catenary. In particular every affinoid
algebra is catenary, and so is every finitely generated algebra over it. Universal catenarity is
the dimension-theoretic half of the excellence of affinoid algebras.

An affinoid algebra is a quotient of a Tate algebra `K⟨X₁, …, Xₙ⟩`. That Tate algebra is a regular
ring (`TauCeti.MvPowerSeries.isRegularRing_isRestricted_subring`), hence Cohen–Macaulay and
universally catenary, and universal catenarity passes to quotients.

The statement includes nonreduced algebras and the zero algebra; no norm or topology on the
affinoid algebra is used.

## References

* B. Conrad, *Irreducible components of rigid spaces*, Ann. Inst. Fourier 49 (1999), 473–541,
  §1.1, for the excellence of affinoid algebras.
* [Stacks Project, Lemma 10.105.9 (00NM)](https://stacks.math.columbia.edu/tag/00NM): Cohen–Macaulay
  rings are universally catenary.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

open TauCeti.Excellence

variable {K A : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CommRing A] [Algebra K A]

/-- **Affinoid algebras are universally catenary.** Every affinoid algebra over a complete
nonarchimedean field is noetherian, and every algebra of finite type over it is catenary. -/
theorem isUniversallyCatenary (hA : IsAffinoidAlgebra K A) : IsUniversallyCatenary A := by
  obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K A).mp hA
  exact π.toRingHom.isUniversallyCatenary_of_surjective hπ

/-- Every affinoid algebra is catenary. -/
example (hA : IsAffinoidAlgebra K A) : IsCatenary A := by
  have := hA.isUniversallyCatenary
  infer_instance

/-- A polynomial ring in finitely many variables over an affinoid algebra is catenary. -/
example (hA : IsAffinoidAlgebra K A) (n : ℕ) : IsCatenary (MvPolynomial (Fin n) A) := by
  have := hA.isUniversallyCatenary
  infer_instance

end TauCeti.IsAffinoidAlgebra
