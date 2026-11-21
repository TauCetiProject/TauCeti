/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Finite
public import TauCeti.Topology.CWComplex.Classical.FiniteCWType
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Compactness
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Manifold
import TauCeti.Geometry.Manifold.Complex.FiniteCWType

/-!
# The free locus inside the compactified quotient

Let `Γ ≤ PSL(2, ℝ)` be discrete. Deleting the elliptic orbits and the adjoined cusps from the
compactified quotient `X(Γ)` leaves exactly the orbit space of the free locus of `Γ`, the
points of `ℍ` with trivial stabilizer. When `X(Γ)` is compact, only finitely many points are
deleted, so the free-locus quotient has finite CW type by the punctured complex-manifold theorem
(`TauCeti.ComplexManifold.instFiniteCWTypeCompl`).

## Main results

* `Subgroup.CompactifiedQuotient.range_ofFreeLocusQuotient`: the free-locus quotient fills the
  compactified quotient outside its elliptic orbits and cusps.
* `Subgroup.CompactifiedQuotient.isOpenEmbedding_ofFreeLocusQuotient`: the free-locus quotient
  is an open subspace of the compactified quotient.
* `Subgroup.CompactifiedQuotient.freeLocusQuotientHomeomorph`: the free-locus quotient is
  homeomorphic to the compactified quotient punctured at its elliptic orbits and cusps.
* `Subgroup.CompactifiedQuotient.finite_ellipticOrbits_union_cusps`: in a compact compactified
  quotient there are finitely many elliptic orbits and cusps.
* `Subgroup.finiteCWType_orbitRel_quotient_freeLocus`: when `X(Γ)` is compact, the orbit space of
  the free locus of `Γ` has finite CW type.
-/

public noncomputable section

open Function MulAction Set TauCeti Topology UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup.CompactifiedQuotient

variable {Γ : Subgroup PSL(2, ℝ)}

variable (Γ) in
/-- The orbit of a point of the free locus, as an interior point of the compactified quotient. -/
def ofFreeLocusQuotient : orbitRel.Quotient Γ (freeLocus Γ ℍ) → Γ.CompactifiedQuotient :=
  Quotient.lift (fun z ↦ ofQuotient (Quotient.mk (orbitRel Γ ℍ) (z : ℍ))) fun a b hab ↦ by
    obtain ⟨g, rfl⟩ := mem_orbit_iff.mp (orbitRel_apply.mp hab)
    exact congrArg ofQuotient (Quotient.sound (orbitRel_apply.mpr ⟨g, rfl⟩))

/-- The orbit of a free point is its orbit in the coarse quotient. -/
@[simp]
theorem ofFreeLocusQuotient_mk (z : freeLocus Γ ℍ) :
    ofFreeLocusQuotient Γ (Quotient.mk _ z) = ofQuotient (Quotient.mk (orbitRel Γ ℍ) (z : ℍ)) :=
  (rfl)

/-- Two free points in the same orbit of `Γ` on `ℍ` are in the same orbit on the free locus. -/
theorem ofFreeLocusQuotient_injective : Injective (ofFreeLocusQuotient Γ) := by
  rintro ⟨a⟩ ⟨b⟩ hab
  obtain ⟨g, hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact (ofQuotient_injective hab)))
  exact Quotient.sound (orbitRel_apply.mpr ⟨g, Subtype.ext hg⟩)

/-- **The free-locus quotient fills the compactified quotient outside its elliptic orbits and
cusps.** An interior orbit comes from the free locus exactly when it is not elliptic, and no cusp
does. -/
theorem range_ofFreeLocusQuotient :
    range (ofFreeLocusQuotient Γ) = (ofQuotient '' Γ.ellipticOrbits ∪ range ofCusp)ᶜ := by
  ext x
  cases x with
  | ofCusp C => simp [ofFreeLocusQuotient]
  | ofQuotient q =>
    induction q using Quotient.inductionOn with
    | h z =>
      simp only [mem_range, mem_compl_iff, mem_union, mem_image,
        ofQuotient_injective.eq_iff, exists_eq_right, quotientMk_mem_ellipticOrbits_iff,
        not_or, not_not, reduceCtorEq, exists_false, not_false_eq_true, and_true]
      constructor
      · rintro ⟨w, hw⟩
        induction w using Quotient.inductionOn with
        | h w =>
          exact (mem_freeLocus_iff_of_quotientMk_eq Γ ℍ (ofQuotient_injective hw)).mp w.property
      · exact fun hz ↦ ⟨Quotient.mk _ ⟨z, hz⟩, rfl⟩

variable [DiscreteTopology Γ]

/-- The inclusion of the free-locus quotient is continuous. -/
theorem continuous_ofFreeLocusQuotient : Continuous (ofFreeLocusQuotient Γ) :=
  (continuous_ofQuotient.comp (continuous_quotient_mk'.comp continuous_subtypeVal)).quotient_lift
    _

/-- The inclusion of the free-locus quotient is open: the free locus is open in `ℍ`, and both
orbit projections and the inclusion of the coarse quotient are open maps. -/
theorem isOpenMap_ofFreeLocusQuotient : IsOpenMap (ofFreeLocusQuotient Γ) :=
  .of_comp continuous_quotient_mk' Quotient.mk_surjective <| isOpenMap_ofQuotient.comp <|
    isOpenMap_quotient_mk'_mul.comp (isOpen_freeLocus Γ ℍ).isOpenMap_subtypeVal

/-- The free-locus quotient is an open subspace of the compactified quotient. -/
theorem isOpenEmbedding_ofFreeLocusQuotient : IsOpenEmbedding (ofFreeLocusQuotient Γ) :=
  .of_continuous_injective_isOpenMap continuous_ofFreeLocusQuotient
    ofFreeLocusQuotient_injective isOpenMap_ofFreeLocusQuotient

variable (Γ) in
/-- **The free-locus quotient is the compactified quotient punctured at its elliptic orbits and
cusps.** -/
def freeLocusQuotientHomeomorph :
    orbitRel.Quotient Γ (freeLocus Γ ℍ) ≃ₜ ↥(ofQuotient '' Γ.ellipticOrbits ∪ range ofCusp)ᶜ :=
  isOpenEmbedding_ofFreeLocusQuotient.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr range_ofFreeLocusQuotient)

/-- The homeomorphism sends a free orbit to its point in the compactified quotient. -/
@[simp]
theorem freeLocusQuotientHomeomorph_apply (q : orbitRel.Quotient Γ (freeLocus Γ ℍ)) :
    (freeLocusQuotientHomeomorph Γ q : Γ.CompactifiedQuotient) = ofFreeLocusQuotient Γ q :=
  (rfl)

/-- A compact compactified quotient has only finitely many elliptic orbits and cusps. -/
theorem finite_ellipticOrbits_union_cusps [CompactSpace Γ.CompactifiedQuotient] :
    (ofQuotient '' Γ.ellipticOrbits ∪ range ofCusp).Finite :=
  have := finite_cuspOrbit (Γ := Γ)
  (Γ.finite_ellipticOrbits.image _).union (finite_range _)

end Subgroup.CompactifiedQuotient

namespace Subgroup

open CompactifiedQuotient in
/-- **The free-locus quotient of a cofinite Fuchsian group has finite CW type.** When `X(Γ)` is
compact, the orbit space of the free locus of `Γ` is homeomorphic to `X(Γ)` with the finitely many
elliptic orbits and cusps deleted. -/
instance finiteCWType_orbitRel_quotient_freeLocus {Γ : Subgroup PSL(2, ℝ)}
    [DiscreteTopology Γ] [CompactSpace Γ.CompactifiedQuotient] :
    FiniteCWType (orbitRel.Quotient Γ (freeLocus Γ ℍ)) :=
  have := (finite_ellipticOrbits_union_cusps (Γ := Γ)).to_subtype
  (freeLocusQuotientHomeomorph Γ).finiteCWType

end Subgroup

end
