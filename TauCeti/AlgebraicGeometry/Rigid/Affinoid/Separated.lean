/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.Presheaf
public import TauCeti.RingTheory.Affinoid.Subdomain.Flat
public import Mathlib.CategoryTheory.Sites.IsSheafFor

/-!
# Unique gluing on finite affinoid covers

The coordinate-algebra presheaf on classical affinoid subdomains is separated for
finite affinoid covers, and more generally for any presieve containing such a cover.
The restriction map into the product of the coordinate algebras of a finite cover
is faithfully flat, so in particular injective. This proves uniqueness of gluing
without discarding nilpotents or assuming that the subdomains are rational.

No existence of gluing is asserted: that is the other half of the sheaf condition.
The empty covering family is included, and can only cover the empty subdomain.
Neither an algebra norm on the ambient algebra nor its affinoidness is needed:
the coordinate algebra of each subdomain is itself affinoid.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§7.2.2 and 8.2.
-/

public section

open CategoryTheory Opposite

namespace TauCeti.AffinoidSubdomain

universe u

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [CommRing A] [Algebra K A]

/-- **Finite affinoid covers are faithfully flat on sections.** The product of the restrictions
from a subdomain to a finite covering family is faithfully flat, including for the empty cover
of the empty subdomain. -/
theorem faithfullyFlat_pi_restrict {ι : Type*} [Finite ι] {V : AffinoidSubdomain K A}
    (U : ι → AffinoidSubdomain K A) (hUV : ∀ i, U i ≤ V)
    (hcover : ∀ x ∈ V, ∃ i, x ∈ U i) :
    (RingHom.pi fun i ↦ (restrict (hUV i)).toRingHom).FaithfullyFlat := by
  apply IsAffinoidSubdomainMap.faithfullyFlat_pi
    (fun i ↦ isAffinoidSubdomainMap_restrict (hUV i)) V.isAffinoidAlgebra
  intro x
  exact hcover _ (V.isAffinoidSubdomainMap.range_maximalSpectrumComap_subset ⟨x, rfl⟩)

/-- Sections are determined by their restrictions to any finite affinoid cover. This is an
extensionality result in the full coordinate algebra, not only modulo its nilradical. -/
theorem sections_ext_of_finite_cover {ι : Type*} [Finite ι] {V : AffinoidSubdomain K A}
    (U : ι → AffinoidSubdomain K A) (hUV : ∀ i, U i ≤ V)
    (hcover : ∀ x ∈ V, ∃ i, x ∈ U i) {s t : V.sections}
    (hst : ∀ i, restrict (hUV i) s = restrict (hUV i) t) : s = t :=
  (faithfullyFlat_pi_restrict U hUV hcover).injective (funext hst)

/-- **Unique gluing on finite affinoid covers.** The underlying type-valued coordinate presheaf
is separated for every presieve containing a finite affinoid covering family. In particular this
applies to covering families with a finite subcover, without any sheaf or acyclicity assumption. -/
theorem isSeparatedFor_of_finite_cover {ι : Type*} [Finite ι] {V : AffinoidSubdomain K A}
    (U : ι → AffinoidSubdomain K A) (hUV : ∀ i, U i ≤ V)
    (hcover : ∀ x ∈ V, ∃ i, x ∈ U i) (R : Presieve V)
    (hR : ∀ i, R (homOfLE (hUV i))) :
    Presieve.IsSeparatedFor (presheaf ⋙ forget (CommAlgCat.{u} K)) R := by
  intro x s t hs ht
  apply sections_ext_of_finite_cover U hUV hcover
  intro i
  exact (hs _ (hR i)).trans (ht _ (hR i)).symm

end TauCeti.AffinoidSubdomain
